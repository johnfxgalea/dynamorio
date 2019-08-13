/*
 * drhit.c
 *
 *  Created on: 17 Nov 2018
 *      Author: john
 */

#include "drhit.h"

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

#include <sys/time.h>

#ifdef DEBUG
#    define ASSERT(x, msg) DR_ASSERT_MSG(x, msg)
#    define LOG(dc, mask, level, ...) dr_log(dc, mask, level, __VA_ARGS__)
#else
#    define ASSERT(x, msg)            /* nothing */
#    define LOG(dc, mask, level, ...) /* nothing */
#endif

#define HASH_BIT_TABLE 13
#define HIT_COUNT_TABLE_SIZE 65536

/* THREAD SLOTS */
#define DRHIT_HIT_SLOT 0
#define DRHIT_RET_SLOT 1
#define DRHIT_TAG_SLOT 2

/*************************************************************************
 * Global Variables
 */

/**
 * Instance count of drhit
 */
static uint drhit_ref_counter = 0;

static drhit_options_t ops_priv;

/**
 * Info related to thread local storage
 */
static reg_id_t tls_raw_reg;
static uint tls_raw_base;
static int tls_idx = -1;

static hashtable_t bb_table;

static app_pc hit_cache_pc = NULL;

static void *rw_lock;

static opnd_t drhit_get_tls_raw_slot_opnd(int slot_idx) {
    return opnd_create_far_base_disp_ex(tls_raw_reg, REG_NULL, REG_NULL, 1,
            tls_raw_base + (slot_idx * (sizeof(void *))), OPSZ_PTR, false, true,
            false);
}

static reg_t drhit_get_spilled(int slot_idx) {

    byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
            + (slot_idx * (sizeof(void *))));

    void **value = (void **) addr;
    return (reg_t) *value;
}

static uint drhit_get_hitcount_hash(intptr_t bb_id) {

    uint hash = ((uint) bb_id) << 1;
    hash &= (HIT_COUNT_TABLE_SIZE - 1);
    DR_ASSERT(hash < HIT_COUNT_TABLE_SIZE);
    return hash;
}

static dr_emit_flags_t drhit_insert_hit(void *drcontext, void *tag,
        instrlist_t *bb, instr_t *where, bool for_trace, bool translating,
        void *user_data) {

    if (!drmgr_is_first_instr(drcontext, where))
        return DR_EMIT_DEFAULT;

    instr_t *instr;

    dr_rwlock_read_lock(rw_lock);
    app_pc bb_pc = instr_get_app_pc(where);
    bool consider = hashtable_lookup(&bb_table, (void *) bb_pc) != NULL;
    dr_rwlock_read_unlock(rw_lock);

    if (!consider)
        return DR_EMIT_DEFAULT;

    reg_id_t scratch_reg;
    drvector_t allowed;
    drreg_init_and_fill_vector(&allowed, false);
    drreg_set_vector_entry(&allowed, DR_REG_XDX, true);
    if (drreg_reserve_aflags(drcontext, bb, where) != DRREG_SUCCESS
            || drreg_reserve_register(drcontext, bb, where, &allowed,
                    &scratch_reg) != DRREG_SUCCESS) {
        DR_ASSERT(false);
    }
    drvector_delete(&allowed);
    DR_ASSERT(scratch_reg == DR_REG_XDX);
    opnd_t scratch_reg_opnd = opnd_create_reg(scratch_reg);


    instr_t *done_label = INSTR_CREATE_label(drcontext);
    opnd_t done_opnd = opnd_create_instr(done_label);

    /* Load hit table */
    opnd_t hit_table_opnd = drhit_get_tls_raw_slot_opnd(DRHIT_HIT_SLOT);
    instr = INSTR_CREATE_mov_ld(drcontext, scratch_reg_opnd, hit_table_opnd);
    instrlist_meta_preinsert(bb, where, instr);

    /* Decrement */
    uint hash = drhit_get_hitcount_hash((intptr_t) bb_pc);
    opnd_t hit_count_opnd = OPND_CREATE_MEM16(scratch_reg,
            hash * sizeof(uint16_t));
    instr = INSTR_CREATE_sub(drcontext, hit_count_opnd,
            opnd_create_immed_uint(1, OPSZ_2));
    instrlist_meta_preinsert(bb, where, instr);

    /* FIX: jumping in common path. */
    DR_ASSERT(hit_cache_pc != NULL);
    instr = INSTR_CREATE_jcc(drcontext, OP_jnz, done_opnd);
    instrlist_meta_preinsert(bb, where, instr);

    instr_t *jmp_back_label = INSTR_CREATE_label(drcontext);
    opnd_t jmp_back_label_opnd = opnd_create_instr(jmp_back_label);

    instrlist_meta_preinsert(bb, where, jmp_back_label);
    instrlist_meta_preinsert(bb, where, done_label);

    /* Store ret to slot */
    opnd_t ret_opnd = drhit_get_tls_raw_slot_opnd(DRHIT_RET_SLOT);
    instr = INSTR_CREATE_mov_imm(drcontext, ret_opnd, jmp_back_label_opnd);
    instrlist_meta_preinsert(bb, jmp_back_label, instr);

    /* Store tag */
    opnd_t tag_opnd = drhit_get_tls_raw_slot_opnd(DRHIT_TAG_SLOT);
    opnd_t tag_immed_opnd = opnd_create_immed_int((intptr_t) tag, OPSZ_PTR);
    instr = INSTR_CREATE_mov_imm(drcontext, tag_opnd, tag_immed_opnd);
    instrlist_meta_preinsert(bb, jmp_back_label, instr);

    drreg_statelessly_restore_app_value(drcontext, bb, DR_REG_NULL, jmp_back_label, done_label, NULL, NULL);
    drreg_statelessly_restore_app_value(drcontext, bb, DR_REG_XAX, jmp_back_label, done_label, NULL, NULL);
    drreg_statelessly_restore_app_value(drcontext, bb, DR_REG_XDX, jmp_back_label, done_label, NULL, NULL);

    /* Jmp to cache */
    DR_ASSERT(hit_cache_pc != NULL);
    instr = INSTR_CREATE_jmp(drcontext, opnd_create_pc(hit_cache_pc));
    instrlist_meta_preinsert(bb, jmp_back_label, instr);


    drreg_unreserve_aflags(drcontext, bb, where);
    drreg_unreserve_register(drcontext, bb, where, scratch_reg);

    return DR_EMIT_DEFAULT;
}

/************************************************************************
 * New Case HANDING
 */

static void drhit_hit() {

    void *tag = (void *)drhit_get_spilled(DRHIT_TAG_SLOT);

    void *drcontext = dr_get_current_drcontext();

    instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
    instr_t *instr = instrlist_first_app(ilist);
    app_pc bb_pc = instr_get_app_pc(instr);
    instrlist_clear_and_destroy(drcontext, ilist);

    uint16_t *hit_counts = (uint16_t *) drmgr_get_tls_field(drcontext, tls_idx);
    uint hash_index = drhit_get_hitcount_hash((intptr_t) bb_pc);
    DR_ASSERT(hit_counts[hash_index] == 0);

    hit_counts[hash_index] = ops_priv.hit_threshold;
    ops_priv.insert_trigger(drcontext, tag, ops_priv.user_data);
}

static app_pc drhit_init_cache() {

    app_pc cache_pc;
    instrlist_t *ilist;
    size_t size;
    instr_t *where;

    void *drcontext = dr_get_current_drcontext();

    ilist = instrlist_create(drcontext);

    opnd_t return_data_opnd = drhit_get_tls_raw_slot_opnd(DRHIT_RET_SLOT);
    where = INSTR_CREATE_jmp_ind(drcontext, return_data_opnd);
    instrlist_meta_append(ilist, where);

    dr_insert_clean_call(drcontext, ilist, where, drhit_hit, false, 0);

    size = dr_page_size();

    /*
     *  Allocate code cache, and set Read-Write-Execute permissions.
     *  The dr_nonheap_alloc function allows you to set permissions.
     */
    cache_pc = (app_pc) dr_nonheap_alloc(size,
    DR_MEMPROT_READ | DR_MEMPROT_WRITE | DR_MEMPROT_EXEC);

    byte *end = instrlist_encode(drcontext, ilist, cache_pc, true);
    instrlist_clear_and_destroy(drcontext, ilist);

    DR_ASSERT(end - cache_pc <= (int ) size);

    /* Change the permission Read-Write-Execute permissions.
     * In particular, we do not need to write the the private cache.
     */
    dr_memory_protect(cache_pc, size, DR_MEMPROT_READ | DR_MEMPROT_EXEC);

    return cache_pc;
}

static void drhit_destroy_fp_cache(app_pc cache_pc) {

    dr_nonheap_free(cache_pc, dr_page_size());
}

/******************************************************************
 * Frag Deletion
 */

static void deleted_frag(void *drcontext, void *tag) {

//    if (drcontext == NULL)
//        return;
//
//    instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
//    instr_t *instr = instrlist_first_app(ilist);
//    app_pc bb_pc = instr_get_app_pc(instr);
//    instrlist_clear_and_destroy(drcontext, ilist);
//
//    dr_rwlock_write_lock(rw_lock);
//
//    bool consider = hashtable_lookup(&bb_table, bb_pc) != NULL;
//
//    if (consider) {
//        hashtable_remove(&bb_table, bb_pc);
//    }
//    dr_rwlock_write_unlock(rw_lock);
}

/************************************************************************
 * INIT
 */

DR_EXPORT void drhit_include_hit_check(void *drcontext, app_pc bb_pc, bool consider) {

    dr_rwlock_write_lock(rw_lock);
    hashtable_remove(&bb_table, bb_pc);

    if (consider) {
        hashtable_add(&bb_table, bb_pc, (void *) 1);
    }
    dr_rwlock_write_unlock(rw_lock);
}

static void drhit_thread_init(void *drcontext) {

    uint16_t *hit_counts = dr_global_alloc(
    HIT_COUNT_TABLE_SIZE * sizeof(uint16_t));

    for (int i = 0; i < HIT_COUNT_TABLE_SIZE; i++) {
        hit_counts[i] = ops_priv.hit_threshold;
    }

    byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
            + (DRHIT_HIT_SLOT * (sizeof(void *))));
    void **addr_hitcount = (void **) addr;
    *addr_hitcount = hit_counts;

    drmgr_set_tls_field(drcontext, tls_idx, (void *) hit_counts);
}

static void drhit_thread_exit(void *drcontext) {

    uint16_t *hit_counts = (uint16_t *) drmgr_get_tls_field(drcontext, tls_idx);
    dr_global_free(hit_counts, HIT_COUNT_TABLE_SIZE * sizeof(uint16_t));
}

/**
 * TODO
 */
DR_EXPORT drhit_status_t drhit_init(drhit_options_t *ops_in) {


    drmgr_init();

    if (ops_in == NULL || ops_in->hit_threshold == 0||
    ops_in->insert_trigger == NULL)
        return DRHIT_ERROR;

    if (drhit_ref_counter == 0) {

        drreg_options_t drreg_ops = { sizeof(drreg_ops), 2, false, NULL,
        true };

        memcpy(&ops_priv, ops_in, sizeof(drhit_options_t));

        drmgr_priority_t priority =
                { sizeof(drmgr_priority_t), DRMGR_PRIORITY_NAME_DRHIT,
                NULL, NULL, DRMGR_PRIORITY_INSERT_DRHIT /* We want to be right before*/};

        if (!drmgr_register_bb_instrumentation_event(
        NULL, drhit_insert_hit, &priority)
                || drreg_init(&drreg_ops) != DRREG_SUCCESS)
            DR_ASSERT(false);

        if (!drmgr_register_thread_init_event(drhit_thread_init)
                || !drmgr_register_thread_exit_event(drhit_thread_exit))
            return DRHIT_ERROR;

        dr_register_delete_event(deleted_frag);

        tls_idx = drmgr_register_tls_field();
        if (tls_idx == -1)
            return DRHIT_ERROR;

        dr_raw_tls_calloc(&(tls_raw_reg), &(tls_raw_base), 3, 0);

        hit_cache_pc = drhit_init_cache(ops_in->insert_trigger,
                ops_in->user_data);

        /**
         * We initialise the hash table that keeps track of defined cases per
         * basic block.
         */
        hashtable_init_ex(&bb_table, HASH_BIT_TABLE, HASH_INTPTR,
        false, false, NULL, NULL, NULL);

        rw_lock = dr_rwlock_create();
    }

    drhit_ref_counter++;
    return DRHIT_SUCCESS;
}

DR_EXPORT drhit_status_t drhit_exit(void) {

    DR_ASSERT(drhit_ref_counter > 0);
    drhit_ref_counter--;

    if (drhit_ref_counter == 0) {

        DR_ASSERT(hit_cache_pc);
        drhit_destroy_fp_cache(hit_cache_pc);

        drmgr_unregister_bb_instrumentation_ex_event(NULL, NULL,
                drhit_insert_hit,
                NULL);

        if (!drmgr_unregister_thread_init_event(drhit_thread_init)
                || !drmgr_unregister_thread_exit_event(drhit_thread_exit))
            return DRHIT_ERROR;

        dr_raw_tls_cfree(tls_raw_base, 3);
        drmgr_unregister_tls_field(tls_idx);
        dr_unregister_delete_event(deleted_frag);
        drreg_exit();

        hashtable_delete(&bb_table);

        dr_rwlock_destroy(rw_lock);
    }

    drmgr_exit();

    return DRHIT_SUCCESS;
}
