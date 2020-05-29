/* **********************************************************
 * Copyright (c) 2013-2020 Google, Inc.   All rights reserved.
 * **********************************************************/

/*
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of Google, Inc. nor the names of its contributors may be
 *   used to endorse or promote products derived from this software without
 *   specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL GOOGLE, INC. OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */

#include "dr_defines.h"
#include "dr_api.h"
#include "drmgr.h"
#include "../drmgr/drmgr_priv.h"
#include "hashtable.h"
#include "drreg.h"
#include "drbbdup.h"
#include <string.h>
#include <stdint.h>
#include "../ext_utils.h"

#ifdef DEBUG
#    define ASSERT(x, msg) DR_ASSERT_MSG(x, msg)
#    define LOG(dc, mask, level, ...) dr_log(dc, mask, level, __VA_ARGS__)
#    define IF_DEBUG(x) x
#else
#    define ASSERT(x, msg) /* nothing */
#    define LOG(dc, mask, level, ...)
#    define IF_DEBUG(x)
#endif

/* DynamoRIO Basic Block Duplication Extension: a code builder that
 * duplicates code of basic blocks and dispatches control according to runtime
 * conditions so that different instrumentation may be efficiently executed.
 */

/* TODO i#4134: ARM not yet supported. */
#ifndef X86
#    error ARM is not yet supported
#endif

#define HASH_BIT_TABLE 13

/* Definitions for drbbdup's hit-table that drives dynamic case handling.
 * Essentially, a hash-table tracks which BBs are frequently encountering
 * new unhandled cases.
 */
#define TABLE_SIZE 65536 /* Must be a power of 2 to perform efficient mod. */

typedef enum {
    DRBBDUP_ENCODING_SLOT = 0, /* Used as a spill slot for dynamic case generation. */
    DRBBDUP_XAX_REG_SLOT = 1,
    DRBBDUP_FLAG_REG_SLOT = 2,
    DRBBDUP_HIT_TABLE_SLOT = 3,
    DRBBDUP_SLOT_COUNT = 4, /* Need to update if more slots are added. */
} drbbdup_thread_slots_t;

/* A scratch register used by drbbdup's dispatcher. */
#define DRBBDUP_SCRATCH_REG DR_REG_XAX

/* Contains information of a case that maps to a copy of a bb. */
typedef struct {
    uintptr_t encoding; /* The encoding specific to the case. */
    bool is_defined;    /* Denotes whether the case is defined. */
} drbbdup_case_t;

/* Contains per bb information required for managing bb copies. */
typedef struct {
    bool enable_dynamic_handling; /* Denotes whether to dynamically generate cases. */
    bool is_gen; /* Denotes whether a new bb copy is dynamically being generated. */
    drbbdup_case_t default_case;
    drbbdup_case_t *cases; /* Is NULL if enable_dup is not set. */
} drbbdup_manager_t;

/* Label types. */
typedef enum {
    DRBBDUP_LABEL_START = 78, /* Denotes the start of a bb copy. */
    DRBBDUP_LABEL_EXIT = 79,  /* Denotes the end of all bb copies. */
} drbbdup_label_t;

typedef struct {
    /* Used to keep track of the current case during drmgr's instrumentation. */
    drbbdup_case_t cur_case;
    uint16_t hit_counts[TABLE_SIZE]; /* Keeps track of hit-counts of unhandled cases. */
} drbbdup_per_thread;

typedef struct {
    /* Used to keep track of the current case during drmgr's instrumentation. */
    drbbdup_manager_t manager;
    /* Used for reg liveness */
    bool is_scratch_reg_live;
    bool is_flags_reg_live;
    /* Used for dup iteration and stitching: */
    uint case_index;
    instr_t *bb_start; /* used for stitching */
    instr_t *pre;      /* used for stitching */
    instr_t *post;     /* used for stitching */
} drbbdup_local_info_t;

static uint ref_count = 0;        /* Instance count of drbbdup. */
static hashtable_t manager_table; /* Maps bbs with book-keeping data. */
static drbbdup_options_t opts;
static void *rw_lock = NULL;

/* For tracking statistics. */
static void *stat_mutex = NULL;
static drbbdup_stats_t stats;

/* An outlined code cache (storing a clean call) for dynamically generating a case. */
static app_pc code_cache_all_live_pc = NULL;
static app_pc code_cache_scratch_live_pc = NULL;
static app_pc code_cache_flag_live_pc = NULL;
static app_pc code_cache_none_live_pc = NULL;

static int tls_idx = -1; /* For thread local storage info. */
static reg_id_t tls_raw_reg;
static uint tls_raw_base;

static bool
drbbdup_encoding_already_included(drbbdup_manager_t *manager, uintptr_t encoding_check,
                                  bool check_default);

static uintptr_t *
drbbdup_get_tls_raw_slot_addr(drbbdup_thread_slots_t slot_idx)
{
    ASSERT(0 <= slot_idx && slot_idx < DRBBDUP_SLOT_COUNT, "out-of-bounds slot index");
    byte *base = dr_get_dr_segment_base(tls_raw_reg);
    return (uintptr_t *)(base + tls_raw_base + slot_idx * sizeof(uintptr_t));
}

static void
drbbdup_set_tls_raw_slot_val(drbbdup_thread_slots_t slot_idx, uintptr_t val)
{
    uintptr_t *addr = drbbdup_get_tls_raw_slot_addr(slot_idx);
    *addr = val;
}

static uintptr_t
drbbdup_get_tls_raw_slot_val(drbbdup_thread_slots_t slot_idx)
{
    uintptr_t *addr = drbbdup_get_tls_raw_slot_addr(slot_idx);
    return *addr;
}

static opnd_t
drbbdup_get_tls_raw_slot_opnd(drbbdup_thread_slots_t slot_idx)
{
    return opnd_create_far_base_disp_ex(tls_raw_reg, REG_NULL, REG_NULL, 1,
                                        tls_raw_base + (slot_idx * (sizeof(void *))),
                                        OPSZ_PTR, false, true, false);
}

static void
drbbdup_spill_register(void *drcontext, instrlist_t *ilist, instr_t *where, int slot_idx,
                       reg_id_t reg_id)
{
    opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);
    instr_t *instr = XINST_CREATE_store(drcontext, slot_opnd, opnd_create_reg(reg_id));
    instrlist_meta_preinsert(ilist, where, instr);
}

static void
drbbdup_restore_register(void *drcontext, instrlist_t *ilist, instr_t *where,
                         int slot_idx, reg_id_t reg_id)
{
    opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);
    instr_t *instr = XINST_CREATE_load(drcontext, opnd_create_reg(reg_id), slot_opnd);
    instrlist_meta_preinsert(ilist, where, instr);
}

/* Returns whether or not instr is a special instruction that must be the last instr in a
 * bb in accordance to DR rules.
 */
static bool
drbbdup_is_special_instr(instr_t *instr)
{
    return instr_is_syscall(instr) || instr_is_cti(instr) || instr_is_ubr(instr) ||
        instr_is_interrupt(instr);
}

/****************************************************************************
 * Duplication
 */

static void
drbbdup_destroy_manager(void *manager_opaque)
{
    drbbdup_manager_t *manager = (drbbdup_manager_t *)manager_opaque;
    ASSERT(manager != NULL, "manager should not be NULL");
    ASSERT(opts.non_default_case_limit > 0, "dup limit should be greater than zero");
    dr_global_free(manager->cases, sizeof(drbbdup_case_t) * opts.non_default_case_limit);
    dr_global_free(manager, sizeof(drbbdup_manager_t));
}

/* Creates a manager, which contains book-keeping data for a fragment.
 * Returns NULL if basic block duplication is not wanted by the user.
 */
static drbbdup_manager_t *
drbbdup_create_manager(void *drcontext, void *tag, instrlist_t *bb)
{
    bool enable_dup = false;
    drbbdup_manager_t *manager = dr_global_alloc(sizeof(drbbdup_manager_t));
    memset(manager, 0, sizeof(drbbdup_manager_t));
    ASSERT(opts.non_default_case_limit > 0, "dup limit should be greater than zero");
    manager->cases =
        dr_global_alloc(sizeof(drbbdup_case_t) * opts.non_default_case_limit);
    memset(manager->cases, 0, sizeof(drbbdup_case_t) * opts.non_default_case_limit);
    manager->enable_dynamic_handling = true;
    manager->is_gen = false;

    ASSERT(opts.set_up_bb_dups != NULL, "set up call-back cannot be NULL");
    manager->default_case.encoding =
        opts.set_up_bb_dups(manager, drcontext, tag, bb, &enable_dup,
                            &manager->enable_dynamic_handling, opts.user_data);
    manager->default_case.is_defined = true;

    /* Set default case regardless whether dups are enabled. */
    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);
    pt->cur_case = manager->default_case;

    if (enable_dup) {
        /* Default case encoding should not be already registered. */
        DR_ASSERT_MSG(
            !drbbdup_encoding_already_included(manager, manager->default_case.encoding,
                                               false /* don't check default case */),
            "default case encoding cannot be already registered");
    } else {
        /* Just delete as dups are not wanted. */
        drbbdup_destroy_manager(manager);
        manager = NULL;
    }

    return manager;
}

static drbbdup_local_info_t *
drbbdup_create_local_info(void *drcontext, instrlist_t *bb,
                          drbbdup_manager_t *manager_to_copy)
{
    bool is_dead;

    drbbdup_local_info_t *local_info =
        dr_thread_alloc(drcontext, sizeof(drbbdup_local_info_t));
    memset(local_info, 0, sizeof(drbbdup_local_info_t));

    memcpy(&local_info->manager, manager_to_copy, sizeof(drbbdup_manager_t));
    local_info->manager.cases =
        dr_thread_alloc(drcontext, sizeof(drbbdup_case_t) * opts.non_default_case_limit);
    memcpy(local_info->manager.cases, manager_to_copy->cases,
           sizeof(drbbdup_case_t) * opts.non_default_case_limit);

    drreg_is_register_dead(drcontext, DRBBDUP_SCRATCH_REG, instrlist_first(bb), &is_dead);
    local_info->is_scratch_reg_live = !is_dead;

    drreg_are_aflags_dead(drcontext, instrlist_first(bb), &is_dead);
    local_info->is_flags_reg_live = !is_dead;

    return local_info;
}

static void
drbbdup_destroy_local_info(void *drcontext, drbbdup_local_info_t *info_to_destroy)
{
    dr_thread_free(drcontext, info_to_destroy->manager.cases,
                   sizeof(drbbdup_case_t) * opts.non_default_case_limit);
    dr_thread_free(drcontext, info_to_destroy, sizeof(drbbdup_local_info_t));
}

/* Returns the number of bb duplications excluding the default case. */
static uint
drbbdup_count(drbbdup_manager_t *manager)
{
    uint count = 0;
    int i;
    ASSERT(manager != NULL, "should not be NULL");
    for (i = 0; i < opts.non_default_case_limit; i++) {
        /* If case is defined, increment the counter. */
        if (manager->cases[i].is_defined)
            count++;
    }

    return count;
}

/* Clone from original instrlist, but place duplication in bb. */
static void
drbbdup_add_copy(void *drcontext, instrlist_t *bb, instrlist_t *orig_bb)
{
    if (instrlist_first(orig_bb) != NULL) {
        instrlist_t *dup = instrlist_clone(drcontext, orig_bb);
        instr_t *start = instrlist_first(dup);
        instrlist_prepend(bb, start);

        /* Empty list and destroy. Do not use clear as instrs are needed. */
        instrlist_init(dup);
        instrlist_destroy(drcontext, dup);
    }
}

/* Transforms the bb to contain additional copies (within the same fragment). */
static void
drbbdup_set_up_copies(void *drcontext, instrlist_t *bb, drbbdup_manager_t *manager)
{
    ASSERT(manager != NULL, "manager should not be NULL");
    ASSERT(manager->cases != NULL, "cases should not be NULL");

    /* Example: Lets say we have the following bb:
     *   mov ebx ecx
     *   mov esi eax
     *   ret
     *
     * We require 2 cases, we need to construct the bb as follows:
     *   LABEL 1
     *   mov ebx ecx
     *   mov esi eax
     *   jmp EXIT LABEL
     *
     *   LABEL 2
     *   mov ebx ecx
     *   mov esi eax
     *   EXIT LABEL
     *   ret
     *
     * The inclusion of the dispatcher is left for the instrumentation stage.
     *
     * Note, we add jmp instructions here and DR will set them to meta automatically.
     */

    /* We create a duplication here to keep track of original bb. */
    instrlist_t *original = instrlist_clone(drcontext, bb);

    /* If the last instruction is a system call/cti, we remove it from the original.
     * This is done so that we do not copy such instructions and abide by DR rules.
     */
    instr_t *last = instrlist_last_app(original);
    app_pc jmp_translation;
    if (drbbdup_is_special_instr(last)) {
        jmp_translation = instr_get_app_pc(last);
        instrlist_remove(original, last);
        instr_destroy(drcontext, last);
    } else {
        jmp_translation =
            (app_pc)decode_next_pc(drcontext, (byte *)instr_get_app_pc(last));
    }

    /* Create an EXIT label. */
    instr_t *exit_label = INSTR_CREATE_label(drcontext);
    opnd_t exit_label_opnd = opnd_create_instr(exit_label);
    instr_set_note(exit_label, (void *)(intptr_t)DRBBDUP_LABEL_EXIT);

    /* Prepend a START label. */
    instr_t *label = INSTR_CREATE_label(drcontext);
    instr_set_note(label, (void *)(intptr_t)DRBBDUP_LABEL_START);
    instrlist_meta_preinsert(bb, instrlist_first(bb), label);

    /* Perform duplication. */
    int num_copies = (int)drbbdup_count(manager);
    ASSERT(num_copies >= 1, "there must be at least one copy");
    int start = num_copies - 1;
    int i;
    for (i = start; i >= 0; i--) {
        /* Prepend a jmp targeting the EXIT label. */
        instr_t *jmp_exit =
            INSTR_XL8(INSTR_CREATE_jmp(drcontext, exit_label_opnd), jmp_translation);
        instrlist_preinsert(bb, instrlist_first(bb), jmp_exit);

        /* Prepend a copy. */
        drbbdup_add_copy(drcontext, bb, original);

        /* Prepend a START label. */
        label = INSTR_CREATE_label(drcontext);
        instr_set_note(label, (void *)(intptr_t)DRBBDUP_LABEL_START);
        instrlist_meta_preinsert(bb, instrlist_first(bb), label);
    }

    /* Delete original. We are done from making further copies. */
    instrlist_clear_and_destroy(drcontext, original);

    /* Add the EXIT label to the last copy of the bb.
     * If there is a syscall, place the exit label prior, leaving the syscall
     * last. Again, this is to abide by DR rules.
     */
    last = instrlist_last(bb);
    if (drbbdup_is_special_instr(last))
        instrlist_meta_preinsert(bb, last, exit_label);
    else
        instrlist_meta_postinsert(bb, last, exit_label);
}

/* Responsible for doing the actual duplications of the bb. */
static bool
drbbdup_duplicate(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                  bool translating, OUT void **local_info_opaque)
{
    drbbdup_local_info_t *local_info = NULL;
    app_pc pc = instr_get_app_pc(instrlist_first_app(bb));
    ASSERT(pc != NULL, "pc cannot be NULL");

    dr_rwlock_write_lock(rw_lock);
    drbbdup_manager_t *manager =
        (drbbdup_manager_t *)hashtable_lookup(&manager_table, pc);

    if (!for_trace && !translating && manager != NULL && !manager->is_gen) {
        /* Remove existing invalid book-keeping data. */
        hashtable_remove(&manager_table, pc);
        manager = NULL;
    }

    /* A manager is created if there does not already exist one that "book-keeps"
     * this basic block (provided the user also wants to duplicate this bb.
     */
    if (manager == NULL) {
        manager = drbbdup_create_manager(drcontext, tag, bb);
        if (manager != NULL)
            hashtable_add(&manager_table, pc, manager);

        if (opts.is_stat_enabled) {
            dr_mutex_lock(stat_mutex);
            if (manager == NULL)
                stats.no_dup_count++;
            else if (!manager->enable_dynamic_handling)
                stats.no_dynamic_handling_count++;
            dr_mutex_unlock(stat_mutex);
        }
    }

    if (manager != NULL) {
        /* Create a local context to avoid further locking. */
        local_info = drbbdup_create_local_info(drcontext, bb, manager);
    }

    dr_rwlock_write_unlock(rw_lock);

    /* Create local info to avoid races. */
    *local_info_opaque = (void *)local_info;
    /* Add the copies. */
    if (local_info != NULL) {
        drbbdup_set_up_copies(drcontext, bb, &local_info->manager);
        local_info->bb_start = instrlist_first(bb);
        return true;
    }

    return false;
}

/****************************************************************************
 * BB Dup Extraction
 */

/* Determines whether or not we reached a special label recognisable by drbbdup. */
static bool
drbbdup_is_at_label(instr_t *check_instr, drbbdup_label_t label)
{
    if (check_instr == NULL)
        return false;

    /* If it is not a meta label just skip! */
    if (!(instr_is_label(check_instr) && instr_is_meta(check_instr)))
        return false;

    /* Notes are inspected to check whether the label is relevant to drbbdup. */
    drbbdup_label_t actual_label =
        (drbbdup_label_t)(uintptr_t)instr_get_note(check_instr);
    return actual_label == label;
}

/* Returns true if at the start of a bb version is reached. */
static bool
drbbdup_is_at_start(instr_t *check_instr)
{
    return drbbdup_is_at_label(check_instr, DRBBDUP_LABEL_START);
}

/* Returns true if at the end of a bb version is reached. */
static bool
drbbdup_is_at_end(instr_t *check_instr)
{
    if (drbbdup_is_at_label(check_instr, DRBBDUP_LABEL_EXIT))
        return true;

    if (instr_is_cti(check_instr)) {
        instr_t *next_instr = instr_get_next(check_instr);
        return drbbdup_is_at_label(next_instr, DRBBDUP_LABEL_START);
    }

    return false;
}

/* Iterates forward to the start of the next bb copy. Returns NULL upon failure. */
static instr_t *
drbbdup_next_start(instr_t *instr)
{
    while (instr != NULL && !drbbdup_is_at_start(instr))
        instr = instr_get_next(instr);

    return instr;
}

static instr_t *
drbbdup_first_app(instrlist_t *bb)
{
    instr_t *instr = instrlist_first_app(bb);
    /* We also check for at end labels, because the jmp inserted by drbbdup is
     * an app instr which should not be considered.
     */
    while (instr != NULL && (drbbdup_is_at_start(instr) || drbbdup_is_at_end(instr)))
        instr = instr_get_next_app(instr);

    return instr;
}

/* Iterates forward to the end of the next bb copy. Returns NULL upon failure. */
static instr_t *
drbbdup_next_end(instr_t *instr)
{
    while (instr != NULL && !drbbdup_is_at_end(instr))
        instr = instr_get_next(instr);

    return instr;
}

static bool
drbbdup_set_pending_case(void *drcontext, drbbdup_local_info_t *local_info)
{

    drbbdup_case_t *case_info = NULL;
    bool found = false;
    if (!found && local_info->case_index < opts.non_default_case_limit) {
        int i;
        for (i = local_info->case_index; i < opts.non_default_case_limit; i++) {
            case_info = &local_info->manager.cases[i];
            if (case_info->is_defined) {
                found = true;
                break;
            }
        }
        /* Take note of new index, as we might have skipped undefined cases. */
        local_info->case_index = i;
    }

    if (!found && local_info->case_index == opts.non_default_case_limit) {
        /* Finished all non-default cases. Now the default case is considered. */
        case_info = &local_info->manager.default_case;
        ASSERT(case_info->is_defined, "default case must be defined");
        found = true;
    }

    if (!found) {
        /* No more pending dups. Return false. */
        return false;
    }

    /* Set the current case. */
    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);
    pt->cur_case = *case_info;

    return true;
}

/* Extracts a single bb copy from the overall bb starting from start.
 * Overall, separate instr lists simplify user call-backs.
 * The returned instr list needs to be stitched back by having drmgr call
 * drbbdup_stitch_bb_copy().
 */
static instrlist_t *
drbbdup_extract_bb_copy(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                        bool translating, void *local_info_opaque)
{
    drbbdup_local_info_t *local_info = (drbbdup_local_info_t *)local_info_opaque;
    ASSERT(local_info != NULL, "local info cannot be NULL");

    if (!drbbdup_set_pending_case(drcontext, local_info))
        return NULL; /* No more pending cases. */

    /* Begin extraction. */
    instrlist_t *case_bb = instrlist_create(drcontext);
    instr_t *start = local_info->bb_start;
    ASSERT(start != NULL, "start instruction cannot be NULL");
    ASSERT(instr_get_note(start) == (void *)DRBBDUP_LABEL_START,
           "start instruction should be a START label");

    local_info->post = drbbdup_next_end(start);
    ASSERT(local_info->post != NULL, "end instruction cannot be NULL");
    ASSERT(!drbbdup_is_at_start(local_info->post), "end cannot be at start");

    /* Also include the last instruction in the bb if it is a
     * syscall/cti instr.
     */
    instr_t *last_instr = instrlist_last(bb);
    if (drbbdup_is_special_instr(last_instr)) {
        instr_t *instr_cpy = instr_clone(drcontext, last_instr);
        instrlist_preinsert(bb, local_info->post, instr_cpy);
    }
    instrlist_cut(bb, local_info->post);
    local_info->pre = start;
    start = instr_get_next(start); /* Skip START label. */
    instrlist_cut(bb, start);
    instrlist_append(case_bb, start);

    return case_bb;
}

/****************************************************************************
 * BB Dup Stitching
 */

/* When control reaches a bb, we need to restore regs used by the dispatcher's jump.
 * This function inserts the restoration landing.
 */
static void
drbbdup_insert_landing_restoration(void *drcontext, instrlist_t *bb, instr_t *where,
                                   drbbdup_local_info_t *local_info)
{
    if (local_info->is_flags_reg_live) {
        drbbdup_restore_register(drcontext, bb, where, 2, DRBBDUP_SCRATCH_REG);
        dr_restore_arith_flags_from_xax(drcontext, bb, where);
    }

    if (local_info->is_scratch_reg_live) {
        drbbdup_restore_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH_REG);
    }
}

#ifdef X86_64
static void
drbbdup_insert_compare_encoding(void *drcontext, instrlist_t *bb, instr_t *where,
                                drbbdup_case_t *current_case, reg_id_t reg_encoding)
{
    opnd_t opnd = opnd_create_abs_addr(&current_case->encoding, OPSZ_PTR);
    instr_t *instr = XINST_CREATE_cmp(drcontext, opnd, opnd_create_reg(reg_encoding));
    instrlist_meta_preinsert(bb, where, instr);
}
#elif X86_32
static void
drbbdup_insert_compare_encoding(void *drcontext, instrlist_t *bb, instr_t *where,
                                drbbdup_case_t *current_case, reg_id_t reg_encoding)
{
    opnd_t opnd = opnd_create_immed_uint(current_case->encoding, OPSZ_PTR);
    instr_t *instr = XINST_CREATE_cmp(drcontext, opnd_create_reg(reg_encoding), opnd);
    instrlist_meta_preinsert(bb, where, instr);
}
#endif

/* Returns whether or not additional cases should be handled by checking if the
 * copy limit, defined by the user, has been reached.
 */
static bool
drbbdup_do_dynamic_handling(drbbdup_manager_t *manager)
{
    drbbdup_case_t *drbbdup_case;
    int i;
    for (i = 0; i < opts.non_default_case_limit; i++) {
        drbbdup_case = &manager->cases[i];
        /* Search for empty undefined slot. */
        if (!drbbdup_case->is_defined)
            return true;
    }

    return false;
}

/* Increments the execution count of bails to default case. */
static void
drbbdup_inc_bail_count()
{
    dr_mutex_lock(stat_mutex);
    stats.bail_count++;
    dr_mutex_unlock(stat_mutex);
}

/* Calculates hash index of a particular bb to access the hit table. */
static uint
drbbdup_get_hitcount_hash(intptr_t bb_id)
{
    uint hash = ((uint)bb_id) & (TABLE_SIZE - 1);
    ASSERT(hash < TABLE_SIZE, "index to hit table should be within bounds");
    return hash;
}

static app_pc
get_fp_cache(bool is_flags_reg_live, bool is_scratch_reg_live)
{

    if (is_flags_reg_live && is_scratch_reg_live)
        return code_cache_all_live_pc;
    else if (is_flags_reg_live && !is_scratch_reg_live)
        return code_cache_flag_live_pc;
    else if (!is_flags_reg_live && is_scratch_reg_live)
        return code_cache_scratch_live_pc;
    else
        return code_cache_none_live_pc;
}

/* Insert trigger for dynamic case handling. */
static void
drbbdup_insert_dynamic_handling(void *drcontext, app_pc translation_pc, void *tag,
                                instrlist_t *bb, instr_t *where,
                                drbbdup_local_info_t *local_info)
{
    instr_t *instr;
    drbbdup_manager_t *manager = &local_info->manager;

    opnd_t drbbdup_opnd = opnd_create_reg(DRBBDUP_SCRATCH_REG);
    instr_t *done_label = INSTR_CREATE_label(drcontext);

    /* Check whether case limit has not been reached. */
    if (drbbdup_do_dynamic_handling(manager)) {
        drbbdup_case_t *default_case = &manager->default_case;
        ASSERT(default_case->is_defined, "default case must be defined");

        /* Jump if runtime encoding matches default encoding.
         * Unknown encoding encountered upon fall-through.
         */
        drbbdup_insert_compare_encoding(drcontext, bb, where, default_case,
                                        DRBBDUP_SCRATCH_REG);
        instr = INSTR_CREATE_jcc(drcontext, OP_jz, opnd_create_instr(done_label));
        instrlist_meta_preinsert(bb, where, instr);

        /* We need DRBBDUP_SCRATCH_REG. Bail on keeping the encoding in the register. */
        opnd_t encoding_opnd = drbbdup_get_tls_raw_slot_opnd(DRBBDUP_ENCODING_SLOT);
        instr = XINST_CREATE_store(drcontext, encoding_opnd, drbbdup_opnd);
        instrlist_meta_preinsert(bb, where, instr);

        app_pc code_cache_pc =
            get_fp_cache(local_info->is_flags_reg_live, local_info->is_scratch_reg_live);

        /* Don't bother insertion if threshold limit is zero. */
        if (opts.hit_threshold > 0) {
            /* Update hit count and check whether threshold is reached. */
            opnd_t hit_table_opnd = drbbdup_get_tls_raw_slot_opnd(DRBBDUP_HIT_TABLE_SLOT);

            /* Load the hit counter table. */
            instr = XINST_CREATE_load(drcontext, drbbdup_opnd, hit_table_opnd);
            instrlist_meta_preinsert(bb, where, instr);

            /* Register hit. */
            uint hash = drbbdup_get_hitcount_hash((intptr_t)translation_pc);
            opnd_t hit_count_opnd =
                OPND_CREATE_MEM16(DRBBDUP_SCRATCH_REG, hash * sizeof(ushort));
            instr = INSTR_CREATE_sub(drcontext, hit_count_opnd,
                                     opnd_create_immed_uint(1, OPSZ_2));
            instrlist_meta_preinsert(bb, where, instr);

            /* Load bb tag to register so that it can be accessed by outlined clean
             * call.
             */
            instrlist_insert_mov_immed_ptrsz(drcontext, (ptr_int_t)tag, drbbdup_opnd, bb,
                                             where, NULL, NULL);

            /* Jump if hit reaches zero. */
            instr = INSTR_CREATE_jcc(drcontext, OP_jz, opnd_create_pc(code_cache_pc));
            instrlist_meta_preinsert(bb, where, instr);

        } else {
            /* Load bb tag to register so that it can be accessed by outlined clean
             * call.
             */
            instrlist_insert_mov_immed_ptrsz(drcontext, (intptr_t)tag, drbbdup_opnd, bb,
                                             instr, NULL, NULL);

            /* Jump to outlined clean call code for new case registration. */
            instr = XINST_CREATE_jump(drcontext, opnd_create_pc(code_cache_pc));
            instrlist_meta_preinsert(bb, where, instr);
        }
    }

    /* XXX i#4215: Use atomic counter when 64-bit sized integers can be used
     * on 32-bit platforms.
     */
    if (opts.is_stat_enabled) {
        /* Insert clean call so that we can lock stat_mutex. */
        dr_insert_clean_call(drcontext, bb, where, (void *)drbbdup_inc_bail_count, false,
                             0);
    }

    instrlist_meta_preinsert(bb, where, done_label);
}

/* At the start of a bb copy, dispatcher code is inserted. The runtime encoding
 * is compared with the encoding of the defined case, and if they match control
 * falls-through to execute the bb. Otherwise, control  branches to the next bb
 * via next_label.
 */
static void
drbbdup_insert_dispatch(void *drcontext, instrlist_t *bb, instr_t *where,
                        drbbdup_local_info_t *local_info, instr_t *next_label,
                        drbbdup_case_t *current_case)
{
    ASSERT(next_label != NULL, "the label to the next bb copy cannot be NULL");

    drbbdup_insert_compare_encoding(drcontext, bb, where, current_case,
                                    DRBBDUP_SCRATCH_REG);

    /* If runtime encoding not equal to encoding of current case,
     * just jump to next.
     */
    instr_t *instr = INSTR_CREATE_jcc(drcontext, OP_jnz, opnd_create_instr(next_label));
    instrlist_meta_preinsert(bb, where, instr);

    /* If fall-through, restore regs back to their original values. */
    drbbdup_insert_landing_restoration(drcontext, bb, where, local_info);
}

/* Inserts code right before the last bb copy which is used to handle the default
 * case. */
static void
drbbdup_insert_dispatch_end(void *drcontext, app_pc translation_pc, void *tag,
                            instrlist_t *bb, instr_t *where,
                            drbbdup_local_info_t *local_info)
{
    drbbdup_manager_t *manager = &local_info->manager;

    /* Check whether dynamic case handling is enabled by the user to handle an unknown
     * case encoding.
     */
    if (manager->enable_dynamic_handling) {
        drbbdup_insert_dynamic_handling(drcontext, translation_pc, tag, bb, where,
                                        local_info);
    }

    /* Last bb version is always the default case. */
    drbbdup_insert_landing_restoration(drcontext, bb, where, local_info);
}

static void
drbbdup_stitch_bb_copy(void *drcontext, void *tag, instrlist_t *bb, instrlist_t *case_bb,
                       bool for_trace, bool translating, void *local_info_opaque)
{
    drbbdup_local_info_t *local_info = (drbbdup_local_info_t *)local_info_opaque;
    ASSERT(local_info != NULL, "local info cannot be NULL");

    /* STEP 1: Stitch case bb back to main instrlist. */
    instr_t *last_instr = instrlist_last(case_bb);
    if (drbbdup_is_special_instr(last_instr)) {
        instrlist_remove(case_bb, last_instr);
        instr_destroy(drcontext, last_instr);
    }

    instrlist_append(case_bb, local_info->post);
    instr_t *instr = instrlist_first(case_bb);
    instrlist_postinsert(bb, local_info->pre, instr);

    instrlist_init(case_bb);
    instrlist_destroy(drcontext, case_bb);

    /* STEP 2: Insert dispatching code. */
    /* Note, when index is equal to opts.non_default_case_limit,
     * the default case is considered.
     */
    ASSERT(local_info->case_index <= opts.non_default_case_limit, "index not in range");

    instr_t *next_bb_label = drbbdup_next_start(local_info->post);
    if (local_info->case_index < opts.non_default_case_limit) {
        drbbdup_case_t *case_info = &local_info->manager.cases[local_info->case_index];
        drbbdup_insert_dispatch(drcontext, bb, instr_get_next(local_info->pre),
                                local_info, next_bb_label, case_info);
    } else {
        /* Finished all non-default cases. Now the default case is considered. */
        ASSERT(local_info->case_index == opts.non_default_case_limit,
               "should be default case's index");
        ASSERT(next_bb_label == NULL, "default case should be last");

        app_pc pc = instr_get_app_pc(drbbdup_first_app(bb));
        drbbdup_insert_dispatch_end(drcontext, pc, tag, bb,
                                    instr_get_next(local_info->pre), local_info);
    }

    /* STEP 3: Prepare for next iter. */
    local_info->bb_start = next_bb_label;
    /* Increment to consider next pending case. */
    local_info->case_index++;
}

/****************************************************************************
 * Runtime Encoding
 *
 * After the analysis phase, the link phase kicks in. The link phase
 * is responsible for linking the flow of execution to bbs
 * based on the case being handled. Essentially, it inserts the dispatcher.
 */

/* Insert encoding of runtime case by invoking user call-back. */
static void
drbbdup_encode_runtime_case_and_clear(void *drcontext, void *tag, instrlist_t *bb,
                                      bool for_trace, bool translating,
                                      void *local_info_opaque)
{
    drbbdup_local_info_t *local_info = (drbbdup_local_info_t *)local_info_opaque;
    ASSERT(local_info != NULL, "local info cannot be NULL");

    instr_t *where = instrlist_first(bb);

    /* XXX i#4134: statistics -- insert code that tracks the number of times the fragment
     * is executed. Runtime case encoding is always placed at the start of the fragment.
     * This is an ideal place for such stat tracking.
     */

    /* Spill scratch register and flags. */
    drbbdup_spill_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH_REG);

    dr_save_arith_flags_to_xax(drcontext, bb, where);
    drbbdup_spill_register(drcontext, bb, where, 2, DRBBDUP_SCRATCH_REG);
    drbbdup_restore_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH_REG);

    /* Encoding is application-specific and therefore we need the user to define the
     * encoding of the runtime case. Therefore, we invoke a user-defined call-back.
     *
     * It could also be that the encoding is done directly and changed on demand.
     * Therefore, the call-back may be NULL.
     */
    if (opts.insert_encode != NULL) {
        /* Note, we could tell the user not to reserve flags and scratch register since
         * drbbdup is doing that already. However, for flexibility/backwards compatibility
         * ease, this might not be the best approach.
         */
        opts.insert_encode(drcontext, tag, bb, where, opts.user_data);
    }

    /* Load the encoding to the scratch register. */
    /* FIXME i#4134: Perform lock if opts.atomic_load_encoding is set. */
    opnd_t scratch_reg_opnd = opnd_create_reg(DRBBDUP_SCRATCH_REG);
    instr_t *instr =
        XINST_CREATE_load(drcontext, scratch_reg_opnd, opts.runtime_case_opnd);
    instrlist_meta_preinsert(bb, where, instr);

    drbbdup_destroy_local_info(drcontext, local_info);

    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);
    pt->cur_case.is_defined = false;
}

/****************************************************************************
 * Dynamic case handling via flushing.
 */

static bool
drbbdup_encoding_already_included(drbbdup_manager_t *manager, uintptr_t encoding_check,
                                  bool check_default)
{
    ASSERT(manager != NULL, "manager cannot be NULL");
    drbbdup_case_t *drbbdup_case;
    int i;
    for (i = 0; i < opts.non_default_case_limit; i++) {
        drbbdup_case = &manager->cases[i];
        if (drbbdup_case->is_defined && drbbdup_case->encoding == encoding_check)
            return true;
    }

    /* Check default case. */
    if (check_default) {
        drbbdup_case = &manager->default_case;
        if (drbbdup_case->is_defined && drbbdup_case->encoding == encoding_check)
            return true;
    }

    /* We checked all cases, including the default case, and failed to find
     * the encoding.
     */
    return false;
}

static bool
drbbdup_include_encoding(drbbdup_manager_t *manager, uintptr_t new_encoding)
{
    int i;
    drbbdup_case_t *dup_case;
    for (i = 0; i < opts.non_default_case_limit; i++) {
        dup_case = &manager->cases[i];
        if (!dup_case->is_defined) {
            dup_case->is_defined = true;
            dup_case->encoding = new_encoding;
            return true;
        }
    }
    return false;
}

static void
drbbdup_prepare_redirect(dr_mcontext_t *mcontext, drbbdup_manager_t *manager,
                         app_pc bb_pc)
{
    /* Restore flags and scratch reg to their original app values. */
    reg_t val = (reg_t)drbbdup_get_tls_raw_slot_val(DRBBDUP_FLAG_REG_SLOT);
    mcontext->xflags = dr_merge_arith_flags(mcontext->xflags, val);

    reg_set_value(DRBBDUP_SCRATCH_REG, mcontext,
                  (reg_t)drbbdup_get_tls_raw_slot_val(DRBBDUP_XAX_REG_SLOT));

    mcontext->pc = bb_pc; /* redirect execution to the start of the bb. */
}

static void
drbbdup_handle_new_case()
{
    void *drcontext = dr_get_current_drcontext();

    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);

    /* Must use DR_MC_ALL due to dr_redirect_execution. */
    dr_mcontext_t mcontext = {
        sizeof(mcontext),
        DR_MC_ALL,
    };
    dr_get_mcontext(drcontext, &mcontext);

    /* Scratch register holds the tag. */
    void *tag = (void *)reg_get_value(DRBBDUP_SCRATCH_REG, &mcontext);

    instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
    app_pc pc = instr_get_app_pc(drbbdup_first_app(ilist));
    ASSERT(pc != NULL, "pc cannot be NULL");

    bool do_flush = false;

    /* Get the missing case. */
    uintptr_t new_encoding = drbbdup_get_tls_raw_slot_val(DRBBDUP_ENCODING_SLOT);

    dr_rwlock_write_lock(rw_lock);
    drbbdup_manager_t *manager =
        (drbbdup_manager_t *)hashtable_lookup(&manager_table, pc);
    ASSERT(manager != NULL, "manager cannot be NULL");
    ASSERT(new_encoding != manager->default_case.encoding,
           "unhandled encoding cannot be the default case");

    /* Could have been turned off potentially by another thread. */
    if (manager->enable_dynamic_handling) {
        /* Case already registered potentially by another thread. */
        if (!drbbdup_encoding_already_included(manager, new_encoding, true)) {
            /* By default, do case gen. */
            bool do_gen = true;
            if (opts.allow_gen != NULL) {
                do_gen =
                    opts.allow_gen(drcontext, tag, ilist, new_encoding,
                                   &manager->enable_dynamic_handling, opts.user_data);
            }
            if (do_gen)
                drbbdup_include_encoding(manager, new_encoding);

            /* Flush only if a new case needs to be generated or
             * dynamic handling has been disabled.
             */
            do_flush = do_gen || !manager->enable_dynamic_handling;
            /* Mark that flushing is happening for drbbdup. */
            if (do_flush)
                manager->is_gen = true;

            if (opts.is_stat_enabled) {
                dr_mutex_lock(stat_mutex);
                if (do_gen)
                    stats.gen_count++;
                if (!manager->enable_dynamic_handling)
                    stats.no_dynamic_handling_count++;
                dr_mutex_unlock(stat_mutex);
            }
        }
    }
    /* Regardless of whether or not flushing is going to happen, redirection will
     * always be performed.
     */
    drbbdup_prepare_redirect(&mcontext, manager, pc);

    dr_rwlock_write_unlock(rw_lock);

    instrlist_clear_and_destroy(drcontext, ilist);

    /* Refresh hit counter. */
    if (opts.hit_threshold > 0) {
        uint hash = drbbdup_get_hitcount_hash((intptr_t)pc);
        DR_ASSERT(pt->hit_counts[hash] == 0);
        pt->hit_counts[hash] = opts.hit_threshold; /* Reset threshold. */
    }

    /* Delete bb fragment. */
    if (do_flush) {
        LOG(drcontext, DR_LOG_ALL, 2,
            "%s Found new case! Going to flush bb with"
            "pc %p to generate a copy to handle the new case.\n",
            __FUNCTION__, pc);

        /* No locks held upon fragment deletion. */
        /* XXX i#3778: To include once we support specific fragment deletion. */

        dr_unlink_flush_fragment(tag);
    }

    dr_redirect_execution(&mcontext);
}

static app_pc
create_fp_cache(void (*clean_call_func)(), bool is_flags_reg_live,
                bool is_scratch_reg_live)
{
    app_pc cache_pc;
    instrlist_t *ilist;
    void *drcontext = dr_get_current_drcontext();
    size_t size = dr_page_size();
    ilist = instrlist_create(drcontext);

    instr_t *where = INSTR_CREATE_label(drcontext);
    instrlist_meta_append(ilist, where);

    /* Restore flags and scratch reg to their original app values. */
    if (is_flags_reg_live) {
        drbbdup_restore_register(drcontext, ilist, where, DRBBDUP_FLAG_REG_SLOT,
                                 DRBBDUP_SCRATCH_REG);
        dr_restore_arith_flags_from_xax(drcontext, ilist, where);
    }

    if (is_scratch_reg_live) {
        drbbdup_restore_register(drcontext, ilist, where, DRBBDUP_XAX_REG_SLOT,
                                 DRBBDUP_SCRATCH_REG);
    }

    dr_insert_clean_call(drcontext, ilist, where, (void *)clean_call_func, false, 0);

    /* Allocate code cache, and set Read-Write-Execute permissions using
     * dr_nonheap_alloc function.
     */
    cache_pc = (app_pc)dr_nonheap_alloc(
        size, DR_MEMPROT_READ | DR_MEMPROT_WRITE | DR_MEMPROT_EXEC);
    byte *end = instrlist_encode(drcontext, ilist, cache_pc, true);
    DR_ASSERT(end - cache_pc <= (int)size);

    instrlist_clear_and_destroy(drcontext, ilist);

    /* Change the permission Read-Write-Execute permissions. */
    dr_memory_protect(cache_pc, size, DR_MEMPROT_READ | DR_MEMPROT_EXEC);

    return cache_pc;
}

static void
destroy_fp_cache(app_pc cache_pc)
{
    ASSERT(cache_pc, "Code cache should not be NULL");
    dr_nonheap_free(cache_pc, dr_page_size());
}

static bool
init_fp_caches()
{

    bool succ = true;
    code_cache_all_live_pc = create_fp_cache(drbbdup_handle_new_case, true, true);
    succ &= code_cache_all_live_pc != NULL;

    code_cache_scratch_live_pc = create_fp_cache(drbbdup_handle_new_case, false, true);
    succ &= code_cache_scratch_live_pc != NULL;

    code_cache_flag_live_pc = create_fp_cache(drbbdup_handle_new_case, true, false);
    succ &= code_cache_flag_live_pc != NULL;

    code_cache_none_live_pc = create_fp_cache(drbbdup_handle_new_case, false, false);
    succ &= code_cache_none_live_pc != NULL;

    return succ;
}

static void
exit_fp_caches()
{

    destroy_fp_cache(code_cache_all_live_pc);
    destroy_fp_cache(code_cache_scratch_live_pc);
    destroy_fp_cache(code_cache_flag_live_pc);
    destroy_fp_cache(code_cache_none_live_pc);
}

/****************************************************************************
 * INTERFACE
 */

drbbdup_status_t
drbbdup_register_case_encoding(void *drbbdup_ctx, uintptr_t encoding)
{
    if (ref_count == 0)
        return DRBBDUP_ERROR_NOT_INITIALIZED;

    drbbdup_manager_t *manager = (drbbdup_manager_t *)drbbdup_ctx;

    /* Don't check default case because it is not yet set. */
    if (drbbdup_encoding_already_included(manager, encoding, false))
        return DRBBDUP_ERROR_CASE_ALREADY_REGISTERED;

    if (drbbdup_include_encoding(manager, encoding))
        return DRBBDUP_SUCCESS;
    else
        return DRBBDUP_ERROR_CASE_LIMIT_REACHED;
}

drbbdup_status_t
drbbdup_get_current_case_encoding(void *drcontext, OUT uintptr_t *cur_case)
{
    if (cur_case == NULL)
        return DRBBDUP_ERROR_INVALID_PARAMETER;

    if (drmgr_current_bb_phase(drcontext) == DRMGR_PHASE_NONE)
        return DRBBDUP_ERROR_NO_INSTRUM;

    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);

    if (!pt->cur_case.is_defined)
        return DRBBDUP_ERROR_NO_CASE;

    *cur_case = pt->cur_case.encoding;

    return DRBBDUP_SUCCESS;
}

drbbdup_status_t
drbbdup_get_stats(OUT drbbdup_stats_t *stats_in)
{
    if (!opts.is_stat_enabled)
        return DRBBDUP_ERROR_UNSET_FEATURE;
    if (stats_in == NULL || stats_in->struct_size == 0 ||
        stats_in->struct_size > stats.struct_size)
        return DRBBDUP_ERROR_INVALID_PARAMETER;

    dr_mutex_lock(stat_mutex);
    memcpy(stats_in, &stats, stats_in->struct_size);
    dr_mutex_unlock(stat_mutex);
    return DRBBDUP_SUCCESS;
}

/****************************************************************************
 * THREAD INIT AND EXIT
 */

static void
drbbdup_thread_init(void *drcontext)
{
    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)dr_thread_alloc(drcontext, sizeof(drbbdup_per_thread));
    pt->cur_case.is_defined = false;
    /* Init hit table. */
    for (int i = 0; i < TABLE_SIZE; i++)
        pt->hit_counts[i] = opts.hit_threshold;
    drbbdup_set_tls_raw_slot_val(DRBBDUP_HIT_TABLE_SLOT, (uintptr_t)pt->hit_counts);

    drmgr_set_tls_field(drcontext, tls_idx, (void *)pt);
}

static void
drbbdup_thread_exit(void *drcontext)
{
    drbbdup_per_thread *pt =
        (drbbdup_per_thread *)drmgr_get_tls_field(drcontext, tls_idx);
    ASSERT(pt != NULL, "thread-local storage should not be NULL");

    dr_thread_free(drcontext, pt, sizeof(drbbdup_per_thread));
}

/****************************************************************************
 * INIT AND EXIT
 */

static bool
drbbdup_check_options(drbbdup_options_t *ops_in)
{
    if (ops_in != NULL && ops_in->set_up_bb_dups != NULL &&
        ops_in->non_default_case_limit > 0)
        return true;

    return false;
}

static bool
drbbdup_check_case_opnd(opnd_t case_opnd)
{
    /* As stated in the docs, runtime case operand must be a memory reference
     * and pointer-sized.
     */
    if (opnd_is_memory_reference(case_opnd) && opnd_get_size(case_opnd) == OPSZ_PTR)
        return true;

    return false;
}

drbbdup_status_t
drbbdup_init(drbbdup_options_t *ops_in)
{
    /* Return with error if drbbdup has already been initialised. */
    if (ref_count != 0)
        return DRBBDUP_ERROR_ALREADY_INITIALISED;

    if (!drbbdup_check_options(ops_in))
        return DRBBDUP_ERROR_INVALID_PARAMETER;
    if (!drbbdup_check_case_opnd(ops_in->runtime_case_opnd))
        return DRBBDUP_ERROR_INVALID_OPND;

    memcpy(&opts, ops_in, sizeof(drbbdup_options_t));

    drreg_options_t drreg_ops = { sizeof(drreg_ops), 0 /* no regs needed */, false, NULL,
                                  true };

    if (!drmgr_register_bbdup_event(drbbdup_duplicate,
                                    drbbdup_encode_runtime_case_and_clear,
                                    drbbdup_extract_bb_copy, drbbdup_stitch_bb_copy) ||
        !drmgr_register_thread_init_event(drbbdup_thread_init) ||
        !drmgr_register_thread_exit_event(drbbdup_thread_exit) ||
        !dr_raw_tls_calloc(&tls_raw_reg, &tls_raw_base, DRBBDUP_SLOT_COUNT, 0) ||
        drreg_init(&drreg_ops) != DRREG_SUCCESS)
        return DRBBDUP_ERROR;

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1)
        return DRBBDUP_ERROR;

    if (!init_fp_caches())
        return DRBBDUP_ERROR;

    /* Initialise hash table that keeps track of defined cases per
     * basic block.
     */
    hashtable_init_ex(&manager_table, HASH_BIT_TABLE, HASH_INTPTR, false, false,
                      drbbdup_destroy_manager, NULL, NULL);

    rw_lock = dr_rwlock_create();
    if (rw_lock == NULL)
        return DRBBDUP_ERROR;

    if (opts.is_stat_enabled) {
        memset(&stats, 0, sizeof(drbbdup_stats_t));
        stats.struct_size = sizeof(drbbdup_stats_t);
        stat_mutex = dr_mutex_create();
        if (stat_mutex == NULL)
            return DRBBDUP_ERROR;
    }
    ref_count++;

    return DRBBDUP_SUCCESS;
}

drbbdup_status_t
drbbdup_exit(void)
{
    DR_ASSERT(ref_count > 0);
    ref_count--;

    if (ref_count == 0) {
        /* Destroy fast path caches. */
        exit_fp_caches();

        if (!drmgr_unregister_bbdup_event() ||
            !drmgr_unregister_thread_init_event(drbbdup_thread_init) ||
            !drmgr_unregister_thread_exit_event(drbbdup_thread_exit) ||
            !dr_raw_tls_cfree(tls_raw_base, DRBBDUP_SLOT_COUNT) ||
            !drmgr_unregister_tls_field(tls_idx) || drreg_exit() != DRREG_SUCCESS)
            return DRBBDUP_ERROR;

        hashtable_delete(&manager_table);
        dr_rwlock_destroy(rw_lock);
        if (opts.is_stat_enabled)
            dr_mutex_destroy(stat_mutex);
    } else {
        /* Cannot have more than one initialisation of drbbdup. */
        return DRBBDUP_ERROR;
    }

    return DRBBDUP_SUCCESS;
}
