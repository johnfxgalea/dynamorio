/*
 * drbbdup.c
 *
 *  Created on: 17 Nov 2018
 *      Author: john
 */

#include "drbbdup.h"
#include "drbbdup_stat.h" /* To keep track of stats */
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
#include "../ext_utils.h"

/* After three execution of the slow path, we enable fast path generation */

#define HASH_BIT_TABLE 8
#define HIT_COUNT_TABLE_SIZE 4000

/**
 * Instance count of drbbdup
 */

uint drreg_ref_count = 0;

/**
 * Label types.
 */
typedef enum {
    /* The last label denoting the end of duplicated blocks */
    DRBBDUP_LABEL_EXIT = 77,
    /* A label denoting the start/end of a duplicated block */
    DRBBDUP_LABEL_NORMAL = 78,
} drbbdup_label_t;

/*
 * Info related to thread local storage
 */
static reg_id_t tls_raw_reg;
static uint tls_raw_base;

static int tls_idx = -1;

/**
 * A  case map that associated PCs of fragments with case managers.
 *
 * Can't make use of tag identifier of bb because these ids do not
 * transcend over bb creation and deletion over the same app code.
 *
 * Locking needs to be employed since it is global.
 */
static hashtable_t case_manager_table;

/**
 * When a case is not defined and there is an available slot for duplication,
 * drbbdup reads from a faulty page. This leads to a fault, which is handled
 * by drbbdup to define the new case. The bb is flushed, and a new one is created so
 * that the handler of the new case is inserted.
 */
static void *faulty_page = NULL;

/** Global options of drbbdup. **/
static drbbdup_options_t opts;

typedef struct {
    int case_index;
#ifdef    ENABLE_DELAY_FP_GEN
    uint hit_counts[HIT_COUNT_TABLE_SIZE];
#endif
} drbbdup_per_thread;

static opnd_t drbbdup_get_tls_raw_slot_opnd(int slot_idx) {

    return opnd_create_far_base_disp_ex(tls_raw_reg, REG_NULL, REG_NULL, 1,
            tls_raw_base + (slot_idx * (sizeof(void *))),
            OPSZ_PTR, false, true, false);
}

static uint drbbdip_get_hitcount_hash(intptr_t bb_id) {

    return (uint) bb_id & (HIT_COUNT_TABLE_SIZE - 1);
}

/**
 * Returns the value of the comparator.
 */
void* drbbdup_get_comparator() {

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

    return drbbdup_get_tls_raw_slot_opnd(0);
}

static void drbbdup_spill_register(void *drcontext, instrlist_t *ilist,
        instr_t *where, int slot_idx, reg_id_t reg_id) {

    DR_ASSERT(slot_idx > 0);

    opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);
    instr_t *instr = INSTR_CREATE_mov_st(drcontext, slot_opnd,
            opnd_create_reg(reg_id));
    instrlist_meta_preinsert(ilist, where, instr);
}

static void drbbdup_restore_register(void *drcontext, instrlist_t *ilist,
        instr_t *where, int slot_idx, reg_id_t reg_id) {

    DR_ASSERT(slot_idx > 0);

    opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);

    instr_t *instr = INSTR_CREATE_mov_ld(drcontext, opnd_create_reg(reg_id),
            slot_opnd);
    instrlist_meta_preinsert(ilist, where, instr);

}

static reg_t drbbdup_get_spilled(int slot_idx) {

    DR_ASSERT(slot_idx > 0);

    byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
            + (slot_idx * (sizeof(void *))));

    void **value = (void **) addr;
    return (reg_t) *value;
}

/************************************************************************
 * DUPlICATION PHASE
 *
 * This phase is responsible for performing the actual duplications of bbs.
 */

/* Returns the number of bb versions.*/
static uint drbbdup_count_dups(drbbdup_manager_t *manager) {

    DR_ASSERT(manager);

    uint count = 0;
    int i;
    for (i = 0; i < NUMBER_OF_DUPS; i++) {

        /* If case is defined, increment the counter */
        if (manager->cases[i].is_defined)
            count++;
    }

    return count;
}

static bool drbbdup_consider_default(drbbdup_manager_t *manager) {

#ifdef ENABLE_DELAY_FP_GEN
    return true;

#else
    /* Do we need to consider default case now? */
    uint case_count = drbbdup_count_dups(manager);
    return (case_count == NUMBER_OF_DUPS || manager->apply_default);

#endif

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

#ifdef ENABLE_STATS
    if (!translating)
    drbbdup_stat_inc_bb();
#endif

    /* If the first instruction is a branch statement, we simply return.
     * We do not duplicate cti instructions because we need to abide by DR bb rules.
     */
    instr_t *first = instrlist_first(bb);
    if (instr_is_cti(first) || instr_is_ubr(first)) {

#ifdef ENABLE_STATS
        if (!translating)
        drbbdup_stat_inc_non_applicable();
#endif

        return DR_EMIT_DEFAULT;
    }

    /**
     * If the bb is less than the required size, bb duplication is skipped.
     *
     * The intuition here is that small bbs might as well have propagation attempted
     * instead of generating fast paths.
     *
     * For my paper, I set this to 0, i.e. always perform dups.
     * Performing parameter analysis could be left for a mini-project.
     */
    size_t cur_size = 0;
    for (first = instrlist_first_app(bb); first != NULL; first =
            instr_get_next_app(first))
        cur_size++;

    if (cur_size < opts.required_size) {

#ifdef ENABLE_STATS
        if (!translating)
        drbbdup_stat_inc_non_applicable();
#endif

        /** Too small. **/
        return DR_EMIT_DEFAULT;
    }

#ifdef ENABLE_STATS
    if (!translating)
    drbbdup_stat_inc_bb_size(cur_size);
#endif

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
     *   jmp EXIT LABEL
     *
     *   LABEL 2
     *   mov ebx ecx
     *   mov esi eax
     *   jmp EXIT LABEL
     *   EXIT LABEL
     *   ret
     *
     * We will leave the linking for the instrumentation stage.
     *
     * We can add jmp instructions here and DR will set them to meta for us.
     * DR Developers needed to do this for unrolling rep.
     */

    /* We create a duplication here to keep track of original bb */
    instrlist_t *original = instrlist_clone(drcontext, bb);

    instr_t *last = instrlist_last_app(original);

    /**
     * If the last instruction is a sytem call/cti, we remove it from the original.
     * This is done so we do not duplicate these instructions.
     */
    if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)) {
        instrlist_remove(original, last);
        instr_destroy(drcontext, last);
    }

    /* Use the PC of the fragment as the key */
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
        bool consider = opts.create_manager(drcontext, original, manager,
                opts.user_data);

        if (!consider) {

            /** The users doesn't want fast path for this bb. **/

#ifdef ENABLE_STATS
            if (!translating)
            drbbdup_stat_inc_non_applicable();
#endif

            instrlist_clear_and_destroy(drcontext, original);

            /** Destroy the manager. **/
            dr_global_free(manager, sizeof(drbbdup_manager_t));
            hashtable_unlock(&case_manager_table);
            return DR_EMIT_DEFAULT;
        }

        DR_ASSERT(manager->default_case.is_defined);
        hashtable_add(&case_manager_table, pc, manager);
    }

    hashtable_unlock(&case_manager_table);
    DR_ASSERT(manager != NULL);

#ifdef ENABLE_STATS
    if (!translating)
    drbbdup_stat_inc_instrum_bb();
#endif

    drreg_set_bb_properties(drcontext, DRREG_IGNORE_CONTROL_FLOW);

    /* Create exit label */
    instr_t *exit_label = INSTR_CREATE_label(drcontext);
    opnd_t exit_label_opnd = opnd_create_instr(exit_label);
    instr_set_note(exit_label, (void*) (intptr_t) DRBBDUP_LABEL_EXIT);

    /* Add the label of the first bb code that is already in place. */
    instr_t * label = INSTR_CREATE_label(drcontext);
    instr_set_note(label, (void *) (intptr_t) DRBBDUP_LABEL_NORMAL);
    instrlist_meta_preinsert(bb, instrlist_first(bb), label);

    /* Let's perform the duplication */
    uint total_dups = drbbdup_count_dups(manager);

#ifdef ENABLE_DELAY_FP_GEN
    total_dups++;
#else
    if (total_dups == NUMBER_OF_DUPS || manager->apply_default)
    total_dups++;
#endif

    DR_ASSERT(total_dups >= 1);

    /* Now add dups for the cases.*/
    int i;
    for (i = 1; i < total_dups; i++) {

        /** Add the jmp to exit **/
        instr_t *jmp_exit = INSTR_CREATE_jmp(drcontext, exit_label_opnd);
        instrlist_preinsert(bb, instrlist_first(bb), jmp_exit);

        /** Prepend the duplication **/
        drbbdup_add_dup(drcontext, bb, original);

        /** Lastly prepend the Label **/
        label = INSTR_CREATE_label(drcontext);
        instr_set_note(label, (void *) (intptr_t) DRBBDUP_LABEL_NORMAL);
        instrlist_meta_preinsert(bb, instrlist_first(bb), label);
    }

    /* Delete original. We are done from duplication. */
    instrlist_clear_and_destroy(drcontext, original);

    /**
     * Add the exit label for the last instance of the bb.
     * If there is a syscall, place the exit label prior.
     */
    last = instrlist_last(bb);
    if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)) {
        instrlist_meta_preinsert(bb, instrlist_last(bb), exit_label);
    } else {

        /**
         * Restoration at the end of the block is not done automatically
         * by drreg but by drbbdup!
         */
        drreg_set_bb_properties(drcontext, DRREG_IGNORE_BB_END_RESTORE);

        instrlist_meta_postinsert(bb, instrlist_last(bb), exit_label);
    }

    return DR_EMIT_DEFAULT;
}

/************************************************************************
 * ANALYSIS PHASE
 *
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

    /* This is another meta-label used for other purposes. */
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

    DR_ASSERT(start);

    /* Moves to the next dupped bb */
    while (!drbbdup_is_at_end(drcontext, start)) {
        start = instr_get_next(start);
    }

    DR_ASSERT(start);
    return start;
}

static instrlist_t *drbbdup_derive_case_bb(void *drcontext, instrlist_t *bb,
        instr_t **start) {

    /* Extracts the duplicated code for the case */
    instrlist_t *case_bb = instrlist_create(drcontext);

    instr_t *instr = *start;
    while (!drbbdup_is_at_end(drcontext, instr)) {

        /* We avoid including jumps that exit the fast path for analysis */
        if (!(instr_is_cti(instr)
                && drbbdup_is_at_end(drcontext, instr_get_next(instr)))) {
            instr_t *instr_cpy = instr_clone(drcontext, instr);
            instrlist_append(case_bb, instr_cpy);
        }

        instr = instr_get_next(instr);
    }

    *start = instr;
    return case_bb;
}

static void drbbdup_hanlde_pre_analysis(void *drcontext, instrlist_t *bb,
        instr_t *strt, drbbdup_manager_t *manager) {

    /**
     * Trigger pre analysis event.
     * This useful for user to set up things before analysis
     */
    if (!opts.pre_analyse_bb)
        return;

    DR_ASSERT(instr_get_note(strt) == (void * ) DRBBDUP_LABEL_NORMAL);
    strt = instr_get_next(strt);

    instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);
    /** Let the user analyse the BB and set case info **/
    opts.pre_analyse_bb(drcontext, case_bb, manager, opts.user_data);

    instrlist_clear_and_destroy(drcontext, case_bb);
}

static void drbbdup_analyse_one_bb(void *drcontext, instrlist_t *bb,
        instr_t *strt, drbbdup_manager_t *manager, drbbdup_case_t * case_info) {

    instr_t *strt_check = NULL;

    DR_ASSERT(instr_get_note(strt) == (void * ) DRBBDUP_LABEL_NORMAL);
    strt = instr_get_next(strt);

    /**
     * Extract the code of the case.
     * Create separate lists to make it simple for the user
     **/
    instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);
    /** Let the user analyse the BB and set case info **/
    opts.analyse_bb(drcontext, case_bb, manager, case_info, opts.user_data);
    instrlist_clear_and_destroy(drcontext, case_bb);

    strt_check = drbbdup_forward_next(drcontext, bb, strt);
    DR_ASSERT(strt_check == strt); // should point to same instr.

}

static void drbbdup_analyse_bbs(void *drcontext, instrlist_t *bb, instr_t *strt,
        drbbdup_manager_t *manager) {

    /** Instrument default **/
    drbbdup_case_t * case_info = &(manager->default_case);
    DR_ASSERT(case_info);
    DR_ASSERT(case_info->is_defined);

    drbbdup_hanlde_pre_analysis(drcontext, bb, strt, manager);

    if (drbbdup_consider_default(manager))
        drbbdup_analyse_one_bb(drcontext, bb, strt, manager, case_info);

    /** Instrument cases **/
    for (int i = 0; i < NUMBER_OF_DUPS; i++) {

        case_info = &(manager->cases[i]);
        if (case_info->is_defined) {
            drbbdup_analyse_one_bb(drcontext, bb, strt, manager, case_info);
        }
    }
}

static dr_emit_flags_t drbbdup_analyse_phase(void *drcontext, void *tag,
        instrlist_t *bb, bool for_trace, bool translating, void *user_data) {

    app_pc pc = dr_fragment_app_pc(tag);

    /* Fetch hashtable */
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
 * is responsible for linking the flow of execution to bbs
 * based on the case being handled.
 */

static void drbbdup_insert_landing_restoration(void *drcontext, instrlist_t *bb,
        instr_t *where, drbbdup_manager_t *manager) {

    /** When control reached a bb, we need to restore from the JMP **/
    if (!manager->is_eflag_dead) {
        drbbdup_restore_register(drcontext, bb, where, 2, DR_REG_XAX);
        dr_restore_arith_flags_from_xax(drcontext, bb, where);
        drbbdup_restore_register(drcontext, bb, where, 1, DR_REG_XAX);
    }

    if (!manager->is_cmp_reg_dead) {
        drbbdup_restore_register(drcontext, bb, where, 3, DRBBDUP_CMP_REG);
    }
}

static void drbbdup_set_case_labels(void *drcontext, instrlist_t *bb,
        instr_t *strt, drbbdup_manager_t *manager, instr_t** labels) {

    drbbdup_case_t * case_info;

    /* Instrument default (if we need to consider it) */
    if (drbbdup_consider_default(manager)) {
        // Instrument default
        case_info = &(manager->default_case);
        DR_ASSERT(case_info);

        if (case_info->is_defined) {

            DR_ASSERT(instr_is_label(strt));
            void *note = instr_get_note(strt);
            DR_ASSERT(note == (void * ) DRBBDUP_LABEL_NORMAL);

            labels[0] = strt; // record start label
            strt = instr_get_next(strt); // jump to first instr
            strt = drbbdup_forward_next(drcontext, bb, strt); // Forward to next internal bb
        } else {
            DR_ASSERT(false);
        }
    }

    /* Instrument cases. */
    for (int i = 0; i < NUMBER_OF_DUPS; i++) {
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

    /*
     * TODO Look into ways to make this more efficient. Perhaps a jump
     * table but requires more memory. Inlined hash table might also work
     * here but my intuition says it's not the best approach in this case.
     */

    instr_t *labels[(NUMBER_OF_DUPS + 1)];
    memset(labels, 0, sizeof(instr_t *) * (NUMBER_OF_DUPS + 1));
    drbbdup_set_case_labels(drcontext, bb, where, manager, labels);

#ifdef ENABLE_STATS
    drbbdup_stat_clean_bb_exec(drcontext, bb, where);
#endif

    /* Spill register. */
    if (drreg_are_aflags_dead(drcontext, where, &(manager->is_eflag_dead))
            != DRREG_SUCCESS)
        DR_ASSERT(false);

    if (drreg_is_register_dead(drcontext, DRBBDUP_CMP_REG, where,
            &(manager->is_cmp_reg_dead)) != DRREG_SUCCESS)
        DR_ASSERT(false);

    if (!manager->is_eflag_dead) {

        drbbdup_spill_register(drcontext, bb, where, 1, DR_REG_XAX);
        dr_save_arith_flags_to_xax(drcontext, bb, where);
        drbbdup_spill_register(drcontext, bb, where, 2, DR_REG_XAX);
        drbbdup_restore_register(drcontext, bb, where, 1, DR_REG_XAX);
    }

    if (!manager->is_cmp_reg_dead) {

        drbbdup_spill_register(drcontext, bb, where, 3, DRBBDUP_CMP_REG);
    }

    /* Call user function to get comparison */
    opts.get_comparator(drcontext, bb, where, manager, opts.user_data);

    /* Restore unreserved registers */
    drreg_restore_all_now(drcontext, bb, where);

    instr_t *instr;
    opnd_t label_opnd;
    opnd_t opnd;
    opnd_t opnd2;
    instr_t* label;

    bool include_faulty = false;
    drbbdup_case_t *case_info = NULL;

    /**
     * Load the comparator value to register.
     * We could compare directly via addressable mem ref, but this will
     * destroy micro-fusing (mem and immed) !
     */
    opnd_t scratch_reg_opnd = opnd_create_reg(DRBBDUP_CMP_REG);
    opnd = drbbdup_get_comparator_opnd();
    instr = INSTR_CREATE_mov_ld(drcontext, scratch_reg_opnd, opnd);
    instrlist_meta_preinsert(bb, where, instr);

    /* Start from 1 because 0th label is for default */
    int start = 1;

    /** Add cmp and branch sequences **/
    int i;
    for (i = 0; i < NUMBER_OF_DUPS; i++) {

        label = labels[start + i];
        case_info = &(manager->cases[i]);

        if (label != NULL) {

            DR_ASSERT(!include_faulty);
            DR_ASSERT(case_info->is_defined);

            /** Add the comparison **/
            opnd = opnd_create_immed_int((intptr_t) case_info->condition_val,
                    opnd_size_from_bytes(sizeof(case_info->condition_val)));
            instr = INSTR_CREATE_cmp(drcontext, scratch_reg_opnd, opnd);
            instrlist_meta_preinsert(bb, where, instr);

            label_opnd = opnd_create_instr(label);
            instr = INSTR_CREATE_jcc(drcontext, OP_jz, label_opnd);
            instrlist_meta_preinsert(bb, where, instr);

        } else if (!include_faulty) {

            DR_ASSERT(!case_info->is_defined);

            /* No need to add fault again. */
            include_faulty = true;
        }
    }

    if (include_faulty) {

        if (drbbdup_consider_default(manager)) {

            drbbdup_case_t *default_info = &(manager->default_case);
            DR_ASSERT(default_info != NULL);
            DR_ASSERT(default_info->is_defined);
            DR_ASSERT(labels[0] != NULL);
            DR_ASSERT(!case_info->is_defined);

            /* If conditional is not defined, check whether default check
             * does not match and jump to fault.
             */

            opnd = opnd_create_immed_uint(
                    (uintptr_t) default_info->condition_val,
                    opnd_size_from_bytes(sizeof(default_info->condition_val)));
            instr = INSTR_CREATE_cmp(drcontext, scratch_reg_opnd, opnd);
            instrlist_meta_preinsert(bb, where, instr);

            label_opnd = opnd_create_instr(labels[0]);
            instr = INSTR_CREATE_jcc(drcontext, OP_jz, label_opnd);
            instrlist_meta_preinsert(bb, where, instr);

#ifdef ENABLE_DELAY_FP_GEN

            opnd_t hit_table_opnd;
            hit_table_opnd = drbbdup_get_tls_raw_slot_opnd(4);

            /* Load the hit counter table */
            instr = INSTR_CREATE_mov_ld(drcontext, scratch_reg_opnd,
                    hit_table_opnd);
            instrlist_meta_preinsert(bb, where, instr);

            uint hash = drbbdip_get_hitcount_hash((intptr_t) translation);
            opnd_t hit_count_opnd = OPND_CREATE_MEM32(DRBBDUP_CMP_REG, hash *sizeof(uint));

            /* Decrement hit counter */
            opnd = opnd_create_immed_int(1, OPSZ_4);
            instr = INSTR_CREATE_sub(drcontext, hit_count_opnd, opnd);
            instrlist_meta_preinsert(bb, where, instr);

            /* If counter has NOT reached threshold, jmp to default */
            label_opnd = opnd_create_instr(labels[0]);
            instr = INSTR_CREATE_jcc(drcontext, OP_jnz, label_opnd);
            instrlist_meta_preinsert(bb, where, instr);
#endif
        }

        /* Insert faulty instruction here */
        opnd = opnd_create_abs_addr(faulty_page, OPSZ_4);
        opnd2 = opnd_create_immed_uint(1, OPSZ_4);
        instr = INSTR_CREATE_mov_st(drcontext, opnd, opnd2);
        instr_set_translation(instr, translation);
        instrlist_meta_preinsert(bb, where, instr);
    }

#ifdef ENABLE_STATS
    else {

        drbbdup_stat_inc_limit_reached();
        drbbdup_stat_clean_bail_entry(drcontext, bb, where);
    }
#endif
}

static dr_emit_flags_t drbbdup_link_phase(void *drcontext, void *tag,
        instrlist_t *bb, instr_t *instr, bool for_trace, bool translating,
        void *user_data) {

    /* Fetch case manager */
    app_pc pc = dr_fragment_app_pc(tag);

    hashtable_lock(&case_manager_table);
    drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
            &case_manager_table, pc);
    hashtable_unlock(&case_manager_table);

    if (manager == NULL) {
        /** No fast path code wanted! Instrument normally. **/
        opts.instrument_bb(drcontext, bb, instr, NULL, NULL, opts.user_data);
        return DR_EMIT_DEFAULT;
    }

    drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
            drcontext, tls_idx);

    if (!drmgr_is_first_instr(drcontext, instr)) {

        drbbdup_case_t *drbbdup_case = NULL;

        drbbdup_label_t label_info;
        bool result = drbbdup_is_at_end_ex(drcontext, instr, &label_info);
        DR_ASSERT(pt->case_index - 1 < NUMBER_OF_DUPS || pt->case_index == -1);

        if (result && label_info == DRBBDUP_LABEL_NORMAL) {

            /* We have reached the start of a new case */
            bool found = false;
            int i;
            for (i = pt->case_index + 1; i < (NUMBER_OF_DUPS + 1); i++) {

                drbbdup_case = &(manager->cases[i - 1]);

                if (drbbdup_case->is_defined) {
                    found = true;
                    break;
                }
            }

            DR_ASSERT(pt->case_index + 1 == i);
            pt->case_index = i;

            DR_ASSERT(found);

            /* Restore upon entry of considered block */
            drbbdup_insert_landing_restoration(drcontext, bb,
                    instr_get_next(instr), manager);

#ifdef ENABLE_STATS
            drbbdup_stat_clean_case_entry(drcontext, bb, instr_get_next(instr),
                    pt->case_index);
#endif

        } else if (result && label_info == DRBBDUP_LABEL_EXIT) {
            DR_ASSERT(pt->case_index >= 0);

            pt->case_index = -1;
            drreg_restore_all_now(drcontext, bb, instr);

        } else {

            /**
             * Check if we need to restore all spilled register.
             * This is done when we encounter a jump to exit
             */
            if (instr_is_cti(instr) && instr_get_next(instr) != NULL) {

                result = drbbdup_is_at_end_ex(drcontext, instr_get_next(instr),
                        &label_info);

                /* Include restoration before jmp instr */
                if (result && label_info == DRBBDUP_LABEL_NORMAL) {
                    drreg_restore_all_now(drcontext, bb, instr_get_prev(instr));

                    /* Don't bother instrumenting jmp exists of fast paths */
                    return DR_EMIT_DEFAULT;
                }
            }

            if (pt->case_index == -1) {
                drbbdup_case = NULL;
            } else {

                if (pt->case_index == 0) {
                    /* If zero, use default */
                    drbbdup_case = &(manager->default_case);
                } else {
                    /* Otherwise use special case */

                    /* We perform -1 on index to take into account default case. */
                    drbbdup_case = &(manager->cases[pt->case_index - 1]);
                }
            }

            if (instr_is_app(instr))
                opts.instrument_bb(drcontext, bb, instr, manager, drbbdup_case,
                        opts.user_data);
        }
    } else {
        /* Set up entry point to fast paths */

        DR_ASSERT(
                instr_is_label(instr)
                        && instr_get_note(instr)
                                == (void * ) DRBBDUP_LABEL_NORMAL);

        /* Insert jumps prior entry label of  block instance */
        drbbdup_insert_jumps(drcontext, pc, bb, instr, manager);
        /* Insert restoration after entry label of block instance */
        drbbdup_insert_landing_restoration(drcontext, bb, instr_get_next(instr),
                manager);

        /* Set the case to 0. */
        DR_ASSERT(pt->case_index == 0 || pt->case_index == -1);

        if (drbbdup_consider_default(manager)) {
            pt->case_index = 0; // We need to consider default, so start at 0
        } else {
            pt->case_index = 1; // Otherwise, start from first case
        }

#ifdef ENABLE_STATS
        drbbdup_stat_clean_case_entry(drcontext, bb, instr_get_next(instr),
                pt->case_index);
#endif

    }

    return DR_EMIT_DEFAULT;
}

/************************************************************************
 * FAULT HANDING
 */

static bool drbbdup_accessed_faulty_page(byte *target) {

    /**
     * Checks that the access target referred to the faulty page.
     * Otherwise, the fault does not concern drbbdup.
     */
    return faulty_page == (void *) target;
}

static dr_signal_action_t drbbdup_event_signal(void *drcontext,
        dr_siginfo_t *info) {

    if (info->sig == SIGSEGV || info->sig == SIGBUS) {

        byte *target = info->access_address;

        if (drbbdup_accessed_faulty_page(target)) {

#ifdef ENABLE_STATS
            drbbdup_stat_inc_gen();
#endif

            /* Do not use fault fragment data because it could concern a trace.
             * Instead, use the translation.
             */
            app_pc bb_pc = info->mcontext->pc;

            /* Get the missing case */
            reg_t conditional_val = (reg_t) drbbdup_get_comparator();

            /* Look up case manager */
            hashtable_lock(&case_manager_table);

            drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
                    &case_manager_table, bb_pc);

            if (!manager)
                DR_ASSERT_MSG(false, "Cant find manager!\n");

#ifdef  ENABLE_DELAY_FP_GEN
            /* Refresh hit counter*/
            uint hash = drbbdip_get_hitcount_hash((intptr_t) bb_pc);
            drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
                    drcontext, tls_idx);

            DR_ASSERT(pt->hit_counts[hash] == 0);
            pt->hit_counts[hash] = FP_GEN_THRESHOLD;
#endif

            /* Find an undefined case, and set it up for the new conditional. */

            /* Check whether the default case is actually the missing case. */
            if (manager->default_case.condition_val
                    == (unsigned int) (uintptr_t) conditional_val) {

                DR_ASSERT(!manager->apply_default);
                manager->apply_default = true;
            } else {
                int i;
                for (i = 0; i < NUMBER_OF_DUPS; i++) {

                    if (!(manager->cases[i].is_defined)) {

                        manager->cases[i].is_defined = true;
                        manager->cases[i].condition_val =
                                (unsigned int) (uintptr_t) conditional_val;

                        break;
                    } else if (manager->cases[i].condition_val
                            == conditional_val)
                        break;
                }
            }

            hashtable_unlock(&case_manager_table);

            /**
             * This is an important step.
             *
             * In order to handle the new case, we need to flush out the bb
             * in DR's cache. We then redirect execution to app code, which will
             * then lead DR to emit a new bb. This time, the bb will include the handle
             * for our new case which is tracked by the manager.
             */

            bool succ = dr_flush_region(info->mcontext->pc, 1);
            DR_ASSERT(succ);

            if (!manager->is_eflag_dead) {

                // Eflag restoration is taken from drreg. Should move it upon release.
                reg_t newval = info->mcontext->xflags;
                reg_t val;
                uint sahf;

                val = drbbdup_get_spilled(2);
                sahf = (val & 0xff00) >> 8;
                newval &= ~(EFLAGS_ARITH);
                newval |= sahf;
                if (TEST(1, val)) /* seto */
                    newval |= EFLAGS_OF;
                info->mcontext->xflags = newval;

                reg_set_value(DR_REG_XAX, info->mcontext,
                        drbbdup_get_spilled(1));
            }

            if (!manager->is_cmp_reg_dead) {
                reg_set_value(DRBBDUP_CMP_REG, info->mcontext,
                        drbbdup_get_spilled(3));
            }

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

#ifdef    ENABLE_DELAY_FP_GEN
    for (int i = 0; i < HIT_COUNT_TABLE_SIZE; i++){
        pt->hit_counts[i] = FP_GEN_THRESHOLD;
    }

    byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
            + (4 * (sizeof(void *))));
    void **addr_hitcount = (void **) addr;
    *addr_hitcount = pt->hit_counts;
#endif
    drmgr_set_tls_field(drcontext, tls_idx, (void *) pt);
}

static void drbbdup_thread_exit(void *drcontext) {
    drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
            drcontext, tls_idx);

    dr_thread_free(drcontext, pt, sizeof(*pt));
}

static void drbbdup_destroy_manager(void *manager_opaque) {

    drbbdup_manager_t *manager = (drbbdup_manager_t *) manager_opaque;
    dr_global_free(manager, sizeof(drbbdup_manager_t));
}

drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in,
        drmgr_priority_t *bb_instrum_priority) {

    if (drreg_ref_count == 0) {
        DR_ASSERT(ops_in);
        memcpy(&opts, ops_in, sizeof(drbbdup_options_t));

        /* Perform checks */
        DR_ASSERT(opts.create_manager);
        DR_ASSERT(opts.instrument_bb);
        DR_ASSERT(opts.get_comparator);
        DR_ASSERT(opts.analyse_bb);

        /**
         * We initialise the hash table that keeps track of defined cases per
         * basic block.
         */
        hashtable_init_ex(&case_manager_table, HASH_BIT_TABLE, HASH_INTPTR,
        false, false, drbbdup_destroy_manager, NULL, NULL);

        /* Init the faulty page. We access this page when generating fast paths */
        faulty_page = dr_nonheap_alloc(dr_page_size(), DR_MEMPROT_NONE);

        drreg_options_t drreg_ops = { sizeof(drreg_ops), 5, false, NULL, true };

        drmgr_priority_t fault_priority = { sizeof(fault_priority),
        DRMGR_PRIORITY_NAME_FAULT_DRBBDUP,
        NULL, NULL, DRMGR_PRIORITY_FAULT_DRBBDUP };

        if (!drmgr_register_bb_instrumentation_ex_event(drbbdup_duplicate_phase,
                drbbdup_analyse_phase, drbbdup_link_phase, NULL,
                bb_instrum_priority) || drreg_init(&drreg_ops) != DRREG_SUCCESS
                || !drmgr_register_signal_event_ex(drbbdup_event_signal,
                        &fault_priority))
            DR_ASSERT(false);

        if (!drmgr_register_thread_init_event(drbbdup_thread_init)
                || !drmgr_register_thread_exit_event(drbbdup_thread_exit))
            return DRBBDUP_ERROR;

        tls_idx = drmgr_register_tls_field();
        if (tls_idx == -1)
            return DRBBDUP_ERROR;

        /* We make use of three slots for spillage */
        dr_raw_tls_calloc(&(tls_raw_reg), &(tls_raw_base), 5, 0);

    }

    drreg_ref_count++;
    return DRBBDUP_SUCCESS;
}

drbbdup_status_t drbbdup_exit(void) {

    DR_ASSERT(drreg_ref_count > 0);
    drreg_ref_count--;

    if (drreg_ref_count == 0) {

        /* Destroy the faulty page */
        DR_ASSERT(faulty_page);
        dr_nonheap_free(faulty_page, dr_page_size());

        hashtable_delete(&case_manager_table);

        drmgr_unregister_bb_instrumentation_ex_event(drbbdup_duplicate_phase,
                drbbdup_analyse_phase, drbbdup_link_phase, NULL);

        drmgr_unregister_signal_event(drbbdup_event_signal);

        if (!drmgr_unregister_thread_init_event(drbbdup_thread_init)
                || !drmgr_unregister_thread_exit_event(drbbdup_thread_exit))
            return DRBBDUP_ERROR;

        dr_raw_tls_cfree(tls_raw_base, 5);
        drmgr_unregister_tls_field(tls_idx);

        drreg_exit();

#ifdef ENABLE_STATS
        drbbdup_stat_print_stats();
#endif
    }
    return DRBBDUP_SUCCESS;
}
