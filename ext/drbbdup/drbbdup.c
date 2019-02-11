/*
 * drbbdup.c
 *
 *  Created on: 17 Nov 2018
 *      Author: john
 */

#include "drbbdup.h"

#include "dr_api.h"
#include "drreg.h"
#include "drmgr.h"
#include "hashtable.h"
#include <string.h>
#include <limits.h>
#include <stddef.h> /* offsetof */
#include <string.h>
#include <stdint.h>
#include <signal.h>

#define HASH_BIT_TABLE 8

/*  Label types.
 */
typedef enum {
    /* The last label denoting the end of duplicated blocks */
    DRBBDUP_LABEL_EXIT = 77,
    /* A label denoting the start/end of a duplicated block */
    DRBBDUP_LABEL_NORMAL = 78,
} drbbdup_label_t;

reg_id_t tls_raw_reg;
uint tls_raw_base;

/* A  case map that associated PCs of fragments with case managers.
 *
 * Can't make use of tag identifier of bb because these ids do not
 * transcend over bb creation and deletion over the same app code.
 *
 * Locking needs to be employed since it is global.
 */
hashtable_t case_manager_table;

/* When a case is not defined and there is an available slot for duplication,
 * drbbdup reads from a faulty page. This leads to a fault, which is handled
 * by drbbdup to define the new case. The bb is flushed, and a new one is created so
 * that the handler of the new case is inserted.
 */
void *faulty_page = NULL;

/* Global options of drbbdup.
 */
drbbdup_options_t opts;

static int tls_idx = -1;

typedef struct {

    int case_index;
} drbbdup_per_thread;

/* Comparison helpers.
 */

void* drbbdup_get_comparator(void *comparator_val) {

    byte *addr = dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base;
    void **comparator_addr = (void **) addr;
    return *comparator_addr;
}

void drbbdup_set_comparator(void *comparator_val) {

    byte *addr = dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base;
    void **comparator_addr = (void **) addr;
    *comparator_addr = comparator_val;
}

opnd_t drbbdup_get_comparator_opnd() {

    return opnd_create_far_base_disp_ex(tls_raw_reg, REG_NULL, REG_NULL, 1,
            tls_raw_base, OPSZ_PTR, false, true, false);
}

/************************************************************************
 * DUPlICATION PHASE
 *
 * This phase is responsible for performing the actual duplications of the bb.
 *
 * The original code placed by DR is considered as the default case.
 */

/* Returns the number of bb versions.*/
static uint drbbdup_count_dups(drbbdup_manager_t *manager) {
    DR_ASSERT(manager);
    DR_ASSERT(manager->default_case.is_defined);

    /* Include the default case. */
    uint count = 1;

    int i = 0;
    for (i = 0; i < 3; i++) {

        /* If case is defined, increment the counter */
        if (manager->cases[i].is_defined)
            count++;
    }

    return count;
}

static void drbbdup_add_dup(void *drcontext, instrlist_t *bb,
        instrlist_t *original) {

    /* Clone from original instr list, but place duplication in bb. */
    instrlist_t *dup = instrlist_clone(drcontext, original);
    instr_t *start = instrlist_first(dup);
    DR_ASSERT(start);
    instrlist_prepend(bb, start);
    instrlist_init(dup);
    instrlist_destroy(drcontext, dup);
}

static dr_emit_flags_t drbbdup_duplicate_phase(void *drcontext, void *tag,
        instrlist_t *bb, bool for_trace, bool translating, OUT void **user_data) {

    /* If the first instruction is a branch statement, we simply return.
     * We do not duplicate cti instructions because we need to abide by DR bb rules.
     */
    instr_t *first = instrlist_first(bb);
    if (instr_is_cti(first) || instr_is_ubr(first)) {
        return DR_EMIT_DEFAULT;
    }

    /* If the bb is less than the required size, bb duplication is skipped.
     */
    size_t cur_size = 0;
    for (first = instrlist_first_app(bb); first != NULL;
            first = instr_get_next_app(first))
        cur_size++;

    if (cur_size < opts.required_size){
        return DR_EMIT_DEFAULT;
    }


    /* Use the PC of the fragment as the key! */
    app_pc pc = dr_fragment_app_pc(tag);

    /* Fetch new case manager */
    hashtable_lock(&case_manager_table);
    drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
            &case_manager_table, pc);
    if (manager == NULL) {
        /* If manager is not available, we need to create a default one */
        manager = dr_global_alloc(sizeof(drbbdup_manager_t));
        memset(manager, 0, sizeof(drbbdup_manager_t));
        DR_ASSERT(opts.create_manager);
        opts.create_manager(drcontext, bb, manager, opts.user_data);
        DR_ASSERT(manager->default_case.is_defined);

        hashtable_add(&case_manager_table, pc, manager);
    }

    hashtable_unlock(&case_manager_table);
    DR_ASSERT(manager!= NULL);

    /* Let's perform the duplication */
    uint count = drbbdup_count_dups(manager);
    DR_ASSERT(count >= 1);

    /* Example:
     *
     * Lets say the bb is in this form:
     *   mov ebx ecx
     *   mov esi eax
     *   ret
     *
     * We need to perform duplication, adding labels to separate versions.
     * Lets say we require 2 duplications:
     *
     *   LABEL 1
     *   mov ebx ecx
     *   mov esi eax
     *
     *   LABEL 2
     *   mov ebx ecx
     *   mov esi eax
     *
     *   EXIT Label
     *   ret
     *
     * We will leave the linking for the instrumentation stage.
     */

    /* We create a duplication here to keep track of original bb */
    instrlist_t *original = instrlist_clone(drcontext, bb);

    instr_t *last = instrlist_last_app(original);
    /* If the last instruction is a sytem call/cti, we remove it from the original.*/
    if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)) {
        instrlist_remove(original, last);
        instr_destroy(drcontext, last);
    }

    /* Add the label of the first bb code that is already in place. */
    instr_t * label = INSTR_CREATE_label(drcontext);
    instr_set_note(label, (void *) (intptr_t) DRBBDUP_LABEL_NORMAL);
    instrlist_meta_preinsert(bb, instrlist_first(bb), label);

    /* Now add dups for the cases */
    int i;
    for (i = 1; i < count; i++) {

        drbbdup_add_dup(drcontext, bb, original);

        label = INSTR_CREATE_label(drcontext);
        instr_set_note(label, (void *) (intptr_t) DRBBDUP_LABEL_NORMAL);
        instrlist_meta_preinsert(bb, instrlist_first(bb), label);
    }

    /* Delete original */
    instrlist_clear_and_destroy(drcontext, original);

    /* Add the exit label */
    last = instrlist_last(bb);
    label = INSTR_CREATE_label(drcontext);
    instr_set_note(label, (void*) (intptr_t) DRBBDUP_LABEL_EXIT);

    /* If there is a syscall, place the exit label prior. */
    if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)) {
        instrlist_meta_preinsert(bb, instrlist_last(bb), label);
    } else {

        /* Restoration at the end of the block is not done automatically by drreg
         * but by drbbdup!
         */
        drreg_set_bb_properties(drcontext, DRREG_IGNORE_BB_END_RESTORE);

        instrlist_meta_postinsert(bb, instrlist_last(bb), label);
    }

    return DR_EMIT_DEFAULT;
}

/************************************************************************
 * Helper Functions
 */

static bool drbbdup_is_at_end_ex(void *drcontext, instr_t *check_instr,
        drbbdup_label_t *label_info) {

    DR_ASSERT(check_instr != NULL);

    /* if it is not a meta label just skip! */
    if (!instr_is_label(check_instr) || instr_is_app(check_instr))
        return false;

    /* Notes are inspected to check whether the label is relevant. */
    void *note = instr_get_note(check_instr);

    if (note == (void *) DRBBDUP_LABEL_EXIT) {

        *label_info = DRBBDUP_LABEL_EXIT;
        return true;
    } else if (note == (void *) DRBBDUP_LABEL_NORMAL) {

        *label_info = DRBBDUP_LABEL_NORMAL;
        return true;
    }

    /* This is another meta label used for other purposes. */
    return false;
}

/**
 * Returns whether check_instr is the end of the bb. This function
 * is useful when iterating over the duplicated bbs.
 */
static bool drbbdup_is_at_end(void *drcontext, instr_t *check_instr) {

    drbbdup_label_t dump_info;
    return drbbdup_is_at_end_ex(drcontext, check_instr, &dump_info);
}

static instr_t *drbbdup_forward_next(void *drcontext, instrlist_t *bb,
        instr_t *start) {

    /* Moves to the next dupped bb */
    while (!drbbdup_is_at_end(drcontext, start)) {
        start = instr_get_next(start);
    }

    DR_ASSERT(start);
    return start;
}

static instr_t *drbbdup_find_exit_label(void *drcontext, instrlist_t *bb,
        instr_t *start) {

    void *label_info = instr_get_note(start);

    while (label_info != (void *) DRBBDUP_LABEL_EXIT) {

        /* If we encounter a normal label, skip to next. */
        if (label_info == (void *) DRBBDUP_LABEL_NORMAL)
            start = instr_get_next(start);

        start = drbbdup_forward_next(drcontext, bb, start);
        label_info = instr_get_note(start);
    }

    DR_ASSERT(start);
    return start;
}

static instrlist_t *drbbdup_derive_case_bb(void *drcontext, instrlist_t *bb,
        instr_t **start) {

    instrlist_t *case_bb = instrlist_create(drcontext);
    instrlist_init(case_bb);

    instr_t *instr = *start;
    while (!drbbdup_is_at_end(drcontext, instr)) {

        DR_ASSERT(instr_is_app(instr));
        instr_t *instr_cpy = instr_clone(drcontext, instr);
        instrlist_append(case_bb, instr_cpy);
        instr = instr_get_next(instr);
    }

    *start = instr;

    return case_bb;
}

/************************************************************************
 * ANALYSIS PHASE
 *
 */

static void drbbdup_analyse_bbs(void *drcontext, instrlist_t *bb, instr_t *strt,
        drbbdup_manager_t *manager) {

    // Instrument default
    drbbdup_case_t * case_info = &(manager->default_case);
    DR_ASSERT(case_info);
    DR_ASSERT(case_info->is_defined);

    if (case_info->is_defined) {

        strt = instr_get_next(strt);

        instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);
        opts.analyse_bb(drcontext, case_bb, manager, case_info, opts.user_data);
        instrlist_clear_and_destroy(drcontext, case_bb);

        strt = drbbdup_forward_next(drcontext, bb, strt);
    }

    // Instrument cases.
    for (int i = 0; i < 3; i++) {

        case_info = &(manager->cases[i]);
        if (case_info->is_defined) {
            strt = instr_get_next(strt);

            instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);

            opts.analyse_bb(drcontext, case_bb, manager, case_info,
                    opts.user_data);

            instrlist_clear_and_destroy(drcontext, case_bb);

            strt = drbbdup_forward_next(drcontext, bb, strt);
        }
    }
}

static dr_emit_flags_t drbbdup_analyse_phase(void *drcontext, void *tag,
        instrlist_t *bb, bool for_trace, bool translating, void *user_data) {

    app_pc pc = dr_fragment_app_pc(tag);

    hashtable_lock(&case_manager_table);
    drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
            &case_manager_table, pc);
    hashtable_unlock(&case_manager_table);

    if (manager == NULL)
        return DR_EMIT_DEFAULT;

    /* Analyse basic block based on case data. */
    drbbdup_analyse_bbs(drcontext, bb, instrlist_first(bb), manager);

    return DR_EMIT_DEFAULT;
}

/************************************************************************
 * LINK/INSTRUMENTATION PHASE
 *
 * After the analysis phase, the link phase kicks in. The link phase
 * is responsible for linking the flow of execution to dupplicated bbs
 * based on the case being handled.
 */

/* Inserts a jump instruction to the ext label */
static void drbbdup_insert_jmp_to_exit(void *drcontext, instrlist_t *bb,
        instr_t *where, instr_t *exit_label) {

    opnd_t label_opnd = opnd_create_instr(exit_label);
    instr_t *jmp_instr = INSTR_CREATE_jmp(drcontext, label_opnd);
    instrlist_meta_preinsert(bb, where, jmp_instr);
}

static void drbbdup_insert_landing_restoration(void *drcontext, instrlist_t *bb,
        instr_t *where) {

    dr_restore_arith_flags_from_xax(drcontext, bb, where);
    dr_restore_reg(drcontext, bb, where, DR_REG_XAX, SPILL_SLOT_5);
    dr_restore_reg(drcontext, bb, where, DR_REG_XCX, SPILL_SLOT_6);
}

static void drbbdup_set_case_labels(void *drcontext, instrlist_t *bb,
        instr_t *strt, drbbdup_manager_t *manager, instr_t** labels) {

    // Instrument default
    drbbdup_case_t * case_info = &(manager->default_case);
    DR_ASSERT(case_info);

    if (case_info->is_defined) {

        DR_ASSERT(instr_is_label(strt));
        void *note = instr_get_note(strt);
        DR_ASSERT(note == (void * ) DRBBDUP_LABEL_NORMAL);

        labels[0] = strt; // record start label
        strt = instr_get_next(strt); // jump to first app instr
        strt = drbbdup_forward_next(drcontext, bb, strt); // Forward to next internal bb
    } else {
        DR_ASSERT(false);
    }

    /* Instrument cases. */
    for (int i = 0; i < 3; i++) {
        case_info = &(manager->cases[i]);
        if (case_info->is_defined) {

            DR_ASSERT(instr_is_label(strt));
            void *note = instr_get_note(strt);
            DR_ASSERT(note == (void * ) DRBBDUP_LABEL_NORMAL);

            labels[i + 1] = strt;
            strt = instr_get_next(strt);
            strt = drbbdup_forward_next(drcontext, bb, strt);
        } else {
            labels[i + 1] = NULL;
        }
    }
}

static void drbbdup_insert_jumps(void *drcontext, app_pc translation,
        instrlist_t *bb, instr_t *where, drbbdup_manager_t *manager) {

    // TODO Look into ways to make this more efficient. Perhaps a jump table.

    instr_t *labels[4];
    drbbdup_set_case_labels(drcontext, bb, where, manager, labels);

    /* Call user function to get comparison */
    opts.get_comparator(drcontext, bb, where, manager,
            opts.user_data);

    /* Restore unreserved registers */
    drreg_restore_all_now(drcontext, bb, where);

    /* Spill register  */
    dr_save_reg(drcontext, bb, where, DR_REG_XAX, SPILL_SLOT_5);
    dr_save_arith_flags_to_xax(drcontext, bb, where);
    dr_save_reg(drcontext, bb, where, DR_REG_XCX, SPILL_SLOT_6);

    /* Load comparator */

    opnd_t store_opnd = drbbdup_get_comparator_opnd();
    opnd_t comparator_opnd = opnd_create_reg(DR_REG_XCX);
    instrlist_meta_preinsert(bb, where,
            INSTR_CREATE_mov_ld(drcontext, comparator_opnd, store_opnd));

    /* Insert conditional */
    instr_t *instr;
    bool include_faulty = false;
    opnd_t label_opnd;
    opnd_t opnd;
    instr_t* label;

    drbbdup_case_t *default_info = &(manager->default_case);
    drbbdup_case_t *case_info = NULL;

    DR_ASSERT(labels[0] != NULL);
    DR_ASSERT(default_info != NULL);

    int i;
    for (i = 1; i < 4; i++) {

        label = labels[i];
        case_info = &(manager->cases[i - 1]);

        if (label != NULL) {

            DR_ASSERT(case_info->is_defined);

            opnd = opnd_create_immed_int((intptr_t) case_info->condition_val,
                    opnd_size_from_bytes(sizeof(case_info->condition_val)));
            instr = INSTR_CREATE_cmp(drcontext, comparator_opnd, opnd);
            instrlist_meta_preinsert(bb, where, instr);

            label_opnd = opnd_create_instr(label);
            instr = INSTR_CREATE_jcc(drcontext, OP_jz, label_opnd);
            instrlist_meta_preinsert(bb, where, instr);

        } else if (!include_faulty) {

            /* No need to add fault again. */
            include_faulty = true;
        }
    }

    if (include_faulty) {
        /* If conditional is not defined, check whether default check
         * does not match and jump to fault.
         */
        DR_ASSERT(!case_info->is_defined);
        DR_ASSERT(default_info->is_defined);

        opnd = opnd_create_immed_uint((uintptr_t) default_info->condition_val,
                opnd_size_from_bytes(sizeof(default_info->condition_val)));
        instr = INSTR_CREATE_cmp(drcontext, comparator_opnd, opnd);
        instrlist_meta_preinsert(bb, where, instr);

        /* If conditional is not defined, check whether default check
         * does not match and jump to fault.
         */

        label_opnd = opnd_create_instr(labels[0]);
        instr = INSTR_CREATE_jcc(drcontext, OP_jz, label_opnd);
        instrlist_meta_preinsert(bb, where, instr);

        /* If it is not equal, read from faulty page in order to trigger flushing.
         * Ensure the destination register contains the conditional that is not supported,
         * as this is read by the fault handler to get the comparator value.
         */

        opnd = opnd_create_abs_addr(faulty_page, OPSZ_4);
        instr = INSTR_CREATE_mov_ld(drcontext, comparator_opnd, opnd);
        instr_set_translation(instr, translation);
        instrlist_meta_preinsert(bb, where, instr);
    }
}

static dr_emit_flags_t drbbdup_link_phase(void *drcontext, void *tag,
        instrlist_t *bb, instr_t *instr, bool for_trace, bool translating,
        void *user_data) {

    /* Keep track of labels which start dupped bbs. */
    app_pc pc = dr_fragment_app_pc(tag);

    hashtable_lock(&case_manager_table);
    drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
            &case_manager_table, pc);
    hashtable_unlock(&case_manager_table);

    if (manager == NULL) {
        opts.instrument_bb(drcontext, bb, instr, NULL, NULL, opts.user_data);
        return DR_EMIT_DEFAULT;
    }

    drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
            drcontext, tls_idx);

    if (drmgr_is_first_instr(drcontext, instr)) {

        DR_ASSERT(instr_is_label(instr));

        /* Insert jumps. */
        instr_t *first_instr_default_bb = instr_get_next_app(instr);
        app_pc translation = instr_get_app_pc(first_instr_default_bb);
        drbbdup_insert_jumps(drcontext, translation, bb, instr, manager);

        drbbdup_insert_landing_restoration(drcontext, bb,
                instr_get_next(instr));

        // Set the case to 0.
        DR_ASSERT(pt->case_index == 0 || pt->case_index == -1);
        pt->case_index = 0;

    } else {

        drbbdup_case_t *drbbdup_case = NULL;

        drbbdup_label_t label_info;
        bool result = drbbdup_is_at_end_ex(drcontext, instr, &label_info);
        DR_ASSERT(pt->case_index - 1 < 3 || pt->case_index == -1);

        if (result && label_info == DRBBDUP_LABEL_NORMAL) {
            /* We have reached the start of a new case! */

            bool found = false;
            int i;
            for (i = pt->case_index + 1; i < 4; i++) {

                drbbdup_case = &(manager->cases[i - 1]);

                if (drbbdup_case->is_defined) {
                    found = true;
                    break;
                }
            }

            pt->case_index = i;
            DR_ASSERT(found);

            drreg_restore_all_now(drcontext, bb, instr);

            /* Add jmp to exit label prior to the normal label being considered.
             * This is done so the previous bb can correctly exit.
             */
            instr_t *exit_label = drbbdup_find_exit_label(drcontext, bb, instr);
            drbbdup_insert_jmp_to_exit(drcontext, bb, instr, exit_label);

            /* Restore upon entry of considered block */
            drbbdup_insert_landing_restoration(drcontext, bb,
                    instr_get_next(instr));

        } else if (result && label_info == DRBBDUP_LABEL_EXIT) {
            DR_ASSERT(pt->case_index >= 0);

            pt->case_index = -1;
            drreg_restore_all_now(drcontext, bb, instr);

        } else {
            if (pt->case_index == -1) {
                drbbdup_case = NULL;
            } else {

                /* We perform -1 on index to take into account default case. */
                drbbdup_case = &(manager->cases[pt->case_index - 1]);
            }

            opts.instrument_bb(drcontext, bb, instr, manager, drbbdup_case,
                    opts.user_data);
        }
    }

    return DR_EMIT_DEFAULT;

}

/************************************************************************
 * FAULT HANDING
 */

static bool drbbdup_accessed_faulty_page(byte *target) {

    /* Checks that the access target referred to the faulty page.
     * Otherwise, the fault does not concern drbbdup.
     */
    return faulty_page == (void *) target;
}

static dr_signal_action_t drbbdup_event_signal(void *drcontext,
        dr_siginfo_t *info) {

    if (info->sig == SIGSEGV || info->sig == SIGBUS) {
        byte *target = info->access_address;

        if (drbbdup_accessed_faulty_page(target)) {

            /* Get key via dr_fragment_app_pc(). */
            void *tag = info->fault_fragment_info.tag;
            app_pc bb_pc = dr_fragment_app_pc(tag);

            /* Look up case manager */
            hashtable_lock(&case_manager_table);
            drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
                    &case_manager_table, bb_pc);
            hashtable_unlock(&case_manager_table);

            /*
             * Get the conditional value that failed.
             * We know that the register storing the conditional, is the
             * destination of the faulting instruction.
             */
            instr_t * fault_inst = instr_create(drcontext);
            decode(drcontext, info->raw_mcontext->pc, fault_inst);

            DR_ASSERT(instr_get_opcode(fault_inst) == OP_mov_ld);
            opnd_t dst_opnd = instr_get_dst(fault_inst, 0);
            DR_ASSERT(opnd_is_reg(dst_opnd));
            reg_id_t reg = opnd_get_reg(dst_opnd);
            reg_t conditional_val = reg_get_value(reg, info->raw_mcontext);
            instr_destroy(drcontext, fault_inst);
            DR_ASSERT(manager->default_case.condition_val != conditional_val);

            /* Find an undefined case, and set it up for the new conditional. */
            bool found = false;
            int i;
            for (i = 0; i < 3; i++) {

                if (!(manager->cases[i].is_defined)) {
                    manager->cases[i].is_defined = true;
                    found = true;

                    manager->cases[i].condition_val =
                            (unsigned int) (uintptr_t) conditional_val;

                    break;
                }
            }
            DR_ASSERT(found);

            /* This is an important step.
             *
             * In order to handle the new case, we need to flush out the bb
             * in DR's cache. We then redirect execution to app code, which will
             * then lead DR to emit a new bb. This time, the bb will include the handle
             * for our new case which is tracked by the manager.
             *
             * Arbitrary size of 10.
             */
            dr_flush_region(info->mcontext->pc, 10);

            info->raw_mcontext->xflags = info->raw_mcontext->xax;
            reg_set_value(DR_REG_XAX, info->mcontext,
                    dr_read_saved_reg(drcontext, SPILL_SLOT_5));
            reg_set_value(DR_REG_XCX, info->mcontext,
                    dr_read_saved_reg(drcontext, SPILL_SLOT_6));

            return DR_SIGNAL_REDIRECT;
        }
    }

    return DR_SIGNAL_DELIVER;
}

/************************************************************************
 * INIT
 */

static void drbbdup_thread_init(void *drcontext) {
    drbbdup_per_thread *pt = (drbbdup_per_thread *) dr_thread_alloc(drcontext,
            sizeof(*pt));

    pt->case_index = 0;
    drmgr_set_tls_field(drcontext, tls_idx, (void *) pt);

    drbbdup_set_comparator(0);
}

static void drbbdup_thread_exit(void *drcontext) {
    drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
            drcontext, tls_idx);

    dr_thread_free(drcontext, pt, sizeof(*pt));
}

static void drbbdup_destroy_manager(void *manager_opaque) {

    drbbdup_manager_t *manager = (drbbdup_manager_t *) manager_opaque;

    drbbdup_case_t *case_info = &(manager->default_case);
    DR_ASSERT(manager->default_case.is_defined);

    if (opts.destroy_case_user_data && case_info->user_data) {
        opts.destroy_case_user_data(case_info->user_data);
    }

    for (int i = 0; i < 3; i++) {

        case_info = &(manager->cases[i]);

        if (case_info->is_defined) {
            if (opts.destroy_case_user_data && case_info->user_data) {
                opts.destroy_case_user_data(case_info->user_data);
            }
        }
    }

    if (opts.destroy_manager_user_data && manager->user_data)
        opts.destroy_manager_user_data(manager->user_data);

    dr_global_free(manager, sizeof(drbbdup_manager_t));
}

drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in) {

    DR_ASSERT(ops_in);
    memcpy(&opts, ops_in, sizeof(drbbdup_options_t));

    DR_ASSERT(opts.create_manager);
    DR_ASSERT(opts.instrument_bb);
    DR_ASSERT(opts.get_comparator);
    DR_ASSERT(opts.analyse_bb);

    hashtable_init_ex(&case_manager_table, HASH_BIT_TABLE, HASH_INTPTR,
    false, false, drbbdup_destroy_manager, NULL, NULL);

    faulty_page = dr_nonheap_alloc(dr_page_size(), DR_MEMPROT_NONE);

    drreg_options_t drreg_ops;
    drreg_ops.num_spill_slots = 2; // one for comparator and another for aflags.
    drreg_ops.conservative = true;
    drreg_ops.do_not_sum_slots = true;
    drreg_ops.struct_size = sizeof(drreg_options_t);
    drreg_ops.error_callback = NULL;

    drmgr_priority_t priority = { sizeof(drmgr_priority_t),
    DRMGR_PRIORITY_NAME_DRBBDUP,
    NULL, NULL, DRMGR_PRIORITY_DRBBDUP };

    drmgr_priority_t fault_priority = { sizeof(fault_priority),
    DRMGR_PRIORITY_NAME_FAULT_DRBBDUP,
    NULL, NULL, DRMGR_PRIORITY_FAULT_DRBBDUP };

    if (!drmgr_register_bb_instrumentation_ex_event(drbbdup_duplicate_phase,
            drbbdup_analyse_phase, drbbdup_link_phase, NULL, &priority)
            || drreg_init(&drreg_ops) != DRREG_SUCCESS
            || !drmgr_register_signal_event_ex(drbbdup_event_signal,
                    &fault_priority))
        DR_ASSERT(false);

    if (!drmgr_register_thread_init_event(drbbdup_thread_init)
            || !drmgr_register_thread_exit_event(drbbdup_thread_exit))
        return DRBBDUP_ERROR;

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1)
        return DRBBDUP_ERROR;

    dr_raw_tls_calloc(&(tls_raw_reg), &(tls_raw_base), 1, 0);

    return DRBBDUP_SUCCESS;
}

drbbdup_status_t drbbdup_exit(void) {

    DR_ASSERT(faulty_page);
    dr_nonheap_free(faulty_page, dr_page_size());

    hashtable_delete(&case_manager_table);

    drmgr_unregister_bb_instrumentation_ex_event(drbbdup_duplicate_phase,
            drbbdup_analyse_phase, drbbdup_link_phase, NULL);

    drmgr_unregister_signal_event(drbbdup_event_signal);

    if (!drmgr_unregister_thread_init_event(drbbdup_thread_init)
            || !drmgr_unregister_thread_exit_event(drbbdup_thread_exit))
        return DRBBDUP_ERROR;

    dr_raw_tls_cfree(tls_raw_base, 1);
    drmgr_unregister_tls_field(tls_idx);

    drreg_exit();

    return DRBBDUP_SUCCESS;
}
