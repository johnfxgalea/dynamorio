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
#define TABLE_SIZE 32768

/* THREAD SLOTS */
#define DRBBDUP_COMPARATOR_SLOT 0
#define DRBBDUP_XAX_REG_SLOT 1
#define DRBBDUP_FLAG_REG_SLOT 2
#define DRBBDUP_REVERT_TABLE_SLOT 3
#define DRBBDUP_HIT_TABLE_SLOT 4

#define DRBBDUP_SCRATCH DR_REG_XAX

// Comment out macro for no stats
//#define ENABLE_STATS 1

/*************************************************************************
 * Structs
 */

typedef struct {
	drbbdup_options_t functions;
	drbbdup_fp_settings_t fp_settings;
} drbbdup_options_priv_t;

typedef struct {
	unsigned int condition_val;
	bool is_defined;
} drbbdup_case_t;

typedef struct {
	int ref_counter;
	drbbdup_case_t default_case;
	drbbdup_case_t *cases;
	bool is_eflag_dead;
	bool is_xax_dead;
	drbbdup_manager_options_t manager_opts;
} drbbdup_manager_t;

/**
 * Label types.
 */
typedef enum {
	/* The last label denoting the end of duplicated blocks */
	DRBBDUP_LABEL_EXIT = 77,
	/* A label denoting the start of a duplicated block */
	DRBBDUP_LABEL_NORMAL = 78,
} drbbdup_label_t;

typedef struct {
	int case_index;
	void *pre_analysis_data;
	void **instrum_infos;
	uint16_t revert_counts[TABLE_SIZE];
	uint16_t hit_counts[TABLE_SIZE];

} drbbdup_per_thread;

/*************************************************************************
 * Global Variables
 */

/**
 * Instance count of drbbdup
 */
uint drbbdup_ref_count = 0;

/**
 * Info related to thread local storage
 */
static reg_id_t tls_raw_reg;
static uint tls_raw_base;
static int tls_idx = -1;

static hashtable_t case_manager_table;

static drbbdup_options_priv_t opts;

static app_pc fp_new_case_cache_pc = NULL;
static app_pc fp_revert_cache_pc = NULL;
static app_pc fp_stop_revert_cache_pc = NULL;

static void *rw_lock;

/**************************************************************
 * Prototypes
 */

static void
drbbdup_handle_new_case();

/**************************************************************
 * Stats
 */

#ifdef ENABLE_STATS

static void drbbdup_stat_inc_bb();
static void drbbdup_stat_inc_instrum_bb();
static void drbbdup_stat_inc_non_applicable();
static void drbbdup_stat_no_fp();
static void drbbdup_stat_inc_gen();
static void drbbdup_stat_inc_revert();
static void drbbdup_stat_inc_stop_revert();
static void drbbdup_stat_inc_bb_size(uint size);
static void drbbdup_stat_clean_case_entry(void *drcontext, instrlist_t *bb,
		instr_t *where, int case_index);
static void drbbdup_stat_clean_bail_entry(void *drcontext, instrlist_t *bb,
		instr_t *where);
static void drbbdup_stat_popcnt_entry(void *drcontext, instrlist_t *bb,
		instr_t *where);
static void drbbdup_stat_clean_bb_exec(void *drcontext, instrlist_t *bb,
		instr_t *where);
static void drbbdup_stat_print_stats();

static void sample_thread(void *arg);

/** Total number of BB witnessed.**/
static unsigned long total_bb = 0;
/** Total number of BBs with fast path generation. **/
static unsigned long bb_instrumented = 0;
/** Total size of basic blocks (used for avg). **/
static unsigned long total_size = 0;
/** Number of non applicable bbs **/
static unsigned long non_applicable = 0;
/** Number of bbs with no dynamic fp **/
static unsigned long no_fp = 0;
/** Total number of BB executed with faths paths **/
static unsigned long total_exec = 0;
/** Number of fast paths generated **/
static unsigned long gen_num = 0;
/** Number of Reverts **/
static unsigned long revert_num = 0;
/** Number of stop-reverts **/
static unsigned long stop_revert_num = 0;

/** Number of bails to slow path**/
static unsigned long total_bails = 0;

/** Number of popcnt fails to slow path**/
static unsigned long total_popcnt = 0;

/** Number of case entries **/
static unsigned long *case_num = NULL;

static unsigned long prev_full_taint_num = 0;
static unsigned long prev_fp_gen = 0;

void *stat_mutex = NULL;

#define TIME_FILE "./OUT_FILE"
file_t time_file;
#endif

/**************************************************************
 * Helpers
 */
static opnd_t drbbdup_get_tls_raw_slot_opnd(int slot_idx) {

	return opnd_create_far_base_disp_ex(tls_raw_reg, REG_NULL, REG_NULL, 1,
			tls_raw_base + (slot_idx * (sizeof(void *))),
			OPSZ_PTR, false, true, false);
}

DR_EXPORT bool drbbdup_is_reverted(app_pc pc) {

	bool is_reverted = false;

	/* Fetch new case manager */
	dr_rwlock_read_lock(rw_lock);
	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, pc);
	if (manager)
		is_reverted = manager->manager_opts.is_reverted;
	dr_rwlock_read_unlock(rw_lock);

	return is_reverted;
}

/**
 * Returns the value of the comparator.
 */
DR_EXPORT void *
drbbdup_get_comparator() {

	byte *addr = dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base;
	void **comparator_addr = (void **) addr;
	return *comparator_addr;
}

static reg_t drbbdup_get_spilled(int slot_idx) {

	byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
			+ (slot_idx * (sizeof(void *))));

	void **value = (void **) addr;
	return (reg_t) *value;
}

DR_EXPORT void drbbdup_set_comparator(void *comparator_val) {

	byte *addr = dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base;
	void **comparator_addr = (void **) addr;
	*comparator_addr = comparator_val;
}

DR_EXPORT opnd_t drbbdup_get_comparator_opnd() {

	return drbbdup_get_tls_raw_slot_opnd(DRBBDUP_COMPARATOR_SLOT);
}

static void drbbdup_spill_register(void *drcontext, instrlist_t *ilist,
		instr_t *where, int slot_idx, reg_id_t reg_id) {

	opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);
	instr_t *instr = INSTR_CREATE_mov_st(drcontext, slot_opnd,
			opnd_create_reg(reg_id));
	instrlist_meta_preinsert(ilist, where, instr);
}

static void drbbdup_restore_register(void *drcontext, instrlist_t *ilist,
		instr_t *where, int slot_idx, reg_id_t reg_id) {

	opnd_t slot_opnd = drbbdup_get_tls_raw_slot_opnd(slot_idx);
	instr_t *instr = INSTR_CREATE_mov_ld(drcontext, opnd_create_reg(reg_id),
			slot_opnd);
	instrlist_meta_preinsert(ilist, where, instr);
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
	for (i = 0; i < opts.fp_settings.dup_limit; i++) {
		/* If case is defined, increment the counter. */
		if (manager->cases[i].is_defined)
			count++;
	}

	if (manager->default_case.is_defined)
		count++;

	return count;
}

/**
 *  Clone from original instr list, but place duplication in bb.
 */
static void drbbdup_add_dup(void *drcontext, instrlist_t *bb,
		instrlist_t *original) {

	instrlist_t *dup = instrlist_clone(drcontext, original);
	instr_t *start = instrlist_first(dup);
	DR_ASSERT(start);
	instrlist_prepend(bb, start);
	instrlist_init(dup);
	instrlist_destroy(drcontext, dup);
}

static dr_emit_flags_t drbbdup_duplicate_phase(void *drcontext, void *tag,
		instrlist_t *bb, bool for_trace, bool translating) {

	app_pc pc = instr_get_app_pc(instrlist_first_app(bb));

	if (translating)
		return DR_EMIT_DEFAULT;

#ifdef ENABLE_STATS
	if (!for_trace)
	drbbdup_stat_inc_bb();
#endif

	/* Fetch new case manager */
	dr_rwlock_write_lock(rw_lock);
	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, pc);

	/* If reverted, return now */
	if (manager != NULL && manager->manager_opts.is_reverted) {
		dr_rwlock_write_unlock(rw_lock);
		return DR_EMIT_DEFAULT;
	}

	/* If the first instruction is a branch statement, we simply return.
	 * We do not duplicate cti instructions because we need to abide by bb rules -
	 * only one exit.
	 */
	instr_t *first = instrlist_first(bb);
	if (instr_is_syscall(first) || instr_is_cti(first) || instr_is_ubr(first)
			|| instr_is_interrupt(first)) {

		if (manager != NULL)
			hashtable_remove(&case_manager_table, pc);

#ifdef ENABLE_STATS
		drbbdup_stat_inc_non_applicable();
#endif
		dr_rwlock_write_unlock(rw_lock);
		return DR_EMIT_DEFAULT;
	}

	/**
	 * If the bb is less than the required size, bb duplication is skipped.
	 *
	 * The intuition here is that small bbs might as well have propagation attempted
	 * instead of generating fast paths.
	 */
	size_t bb_size = 0;
	for (first = instrlist_first_app(bb); first != NULL; first =
			instr_get_next_app(first))
		bb_size++;

	if (bb_size < opts.fp_settings.required_size) {
		DR_ASSERT(manager == NULL);

#ifdef ENABLE_STATS
		drbbdup_stat_inc_non_applicable();
#endif
		dr_rwlock_write_unlock(rw_lock);
		/** Too small. **/
		return DR_EMIT_DEFAULT;
	}

#ifdef ENABLE_STATS
	drbbdup_stat_inc_bb_size(bb_size);
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
	 *   EXIT LABEL
	 *   ret
	 *
	 * We will leave the linking for the instrumentation stage.
	 *
	 * We can add jmp instructions here and DR will set them to meta for us.
	 * We needed to do this for unrolling rep.
	 */

	if (manager == NULL) {
		/* If manager is not available, we need to create a default one */
		manager = dr_global_alloc(sizeof(drbbdup_manager_t));
		memset(manager, 0, sizeof(drbbdup_manager_t));
		manager->cases = dr_global_alloc(
				sizeof(drbbdup_case_t) * opts.fp_settings.dup_limit);
		memset(manager->cases, 0,
				sizeof(drbbdup_case_t) * opts.fp_settings.dup_limit);
		DR_ASSERT(opts.functions.create_manager);

		manager->manager_opts.enable_dynamic_fp = true;
		manager->manager_opts.enable_pop_threshold = false;
		manager->manager_opts.max_pop_threshold = 0;
		manager->default_case.condition_val = 0;

		manager->manager_opts.enable_revert_check =
				opts.fp_settings.enable_revert;
		manager->manager_opts.is_reverted = false;

		bool consider = opts.functions.create_manager(manager, drcontext, tag,
				bb, &(manager->manager_opts),
				&(manager->default_case.condition_val),
				opts.functions.user_data);

		if (!consider) {
			/** The users doesn't want fast path for this bb. **/
#ifdef ENABLE_STATS
			drbbdup_stat_inc_non_applicable();
#endif

			dr_rwlock_write_unlock(rw_lock);

			/** Destroy the manager. **/
			dr_global_free(manager->cases,
					sizeof(drbbdup_case_t) * opts.fp_settings.dup_limit);
			dr_global_free(manager, sizeof(drbbdup_manager_t));
			return DR_EMIT_DEFAULT;
		}

		manager->default_case.is_defined = true;
		hashtable_add(&case_manager_table, pc, manager);
	}

	/* We create a duplication here to keep track of original bb */
	instrlist_t *original = instrlist_clone(drcontext, bb);
	instr_t *last = instrlist_last_app(original);

	/**
	 * If the last instruction is a sytem call/cti, we remove it from the original.
	 * This is done so we do not duplicate these instructions.
	 */
	if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)
			|| instr_is_interrupt(last)) {
		instrlist_remove(original, last);
		instr_destroy(drcontext, last);
	}

	DR_ASSERT(manager != NULL);

#ifdef ENABLE_STATS
	drbbdup_stat_inc_instrum_bb();
#endif

#ifdef ENABLE_STATS
	if (!manager->manager_opts.enable_dynamic_fp)
	drbbdup_stat_no_fp();
#endif

	/**
	 * Tell drreg to ignore control flow, we are ensuring registers
	 * are live at start of BBs.
	 */
	drreg_set_bb_properties(drcontext, DRREG_IGNORE_CONTROL_FLOW);

	/* Create exit label */
	instr_t *exit_label = INSTR_CREATE_label(drcontext);
	opnd_t exit_label_opnd = opnd_create_instr(exit_label);
	instr_set_note(exit_label, (void *) (intptr_t) DRBBDUP_LABEL_EXIT);

	/** Prepend the Label **/
	instr_t *label = INSTR_CREATE_label(drcontext);
	instr_set_note(label, (void *) (intptr_t) DRBBDUP_LABEL_NORMAL);
	instrlist_meta_preinsert(bb, instrlist_first(bb), label);

	/* Let's perform the duplication */
	int total_dups = (int) drbbdup_count_dups(manager);
	DR_ASSERT(total_dups >= 1);

	/* Now add dups for the cases.*/
	int i;
	for (i = total_dups - 2; i >= 0; i--) {

		/** Add the jmp to exit **/
		instr_t *jmp_exit = INSTR_CREATE_jmp(drcontext, exit_label_opnd);
		instrlist_preinsert(bb, instrlist_first(bb), jmp_exit);

		/** Prepend the duplication **/
		drbbdup_add_dup(drcontext, bb, original);

		/** Prepend the Label **/
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
	if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)
			|| instr_is_interrupt(last)) {

		instrlist_meta_preinsert(bb, last, exit_label);
	} else {

		/**
		 * Restoration at the end of the block is not done automatically
		 * by drreg but by drbbdup! This is because different cases could
		 * have different registers spilled!
		 */
		drreg_set_bb_properties(drcontext, DRREG_IGNORE_BB_END_RESTORE);

		instrlist_meta_postinsert(bb, last, exit_label);
	}

	dr_rwlock_write_unlock(rw_lock);

	return DR_EMIT_STORE_TRANSLATIONS;
}

/************************************************************************
 * ANALYSIS PHASE
 */
static bool drbbdup_is_at_end(instr_t *check_instr, drbbdup_label_t *label_info) {

	DR_ASSERT(check_instr != NULL);

	/* If it is not a meta label just skip! */
	if (!instr_is_label(check_instr) || instr_is_app(check_instr))
		return false;

	/* Notes are inspected to check whether the label is relevant to drbbdup. */
	void *note = instr_get_note(check_instr);

	if (note == (void *) DRBBDUP_LABEL_NORMAL) {

		if (label_info != NULL)
			*label_info = DRBBDUP_LABEL_NORMAL;
		return true;
	} else if (note == (void *) DRBBDUP_LABEL_EXIT) {

		if (label_info != NULL)
			*label_info = DRBBDUP_LABEL_EXIT;
		return true;
	}

	/* This is another meta-label used for other purposes. */
	return false;
}

static instr_t *
drbbdup_forward_next(void *drcontext, instrlist_t *bb, instr_t *start,
		drbbdup_label_t *label_info) {

	DR_ASSERT(start);

	/* Moves to the next dupped bb */
	while (start && !drbbdup_is_at_end(start, label_info)) {
		start = instr_get_next(start);
	}

	return start;
}

static instrlist_t *
drbbdup_derive_case_bb(void *drcontext, instrlist_t *bb, instr_t **start) {

	/* Extracts the duplicated code for the case */
	instrlist_t *case_bb = instrlist_create(drcontext);

	instr_t *instr = *start;
	while (!drbbdup_is_at_end(instr, NULL)) {

		/* We avoid including jumps that exit the fast path for analysis */
		if (!(instr_is_cti(instr)
				&& drbbdup_is_at_end(instr_get_next(instr), NULL))) {
			instr_t *instr_cpy = instr_clone(drcontext, instr);
			instrlist_append(case_bb, instr_cpy);
		}

		instr = instr_get_next(instr);
	}
	*start = instr;

	/* We also need to include the last instruction in the basic block. */
	instr_t *last_instr = instrlist_last(bb);
	if (!drbbdup_is_at_end(last_instr, NULL)) {

		DR_ASSERT(
				instr_is_syscall(last_instr) || instr_is_cti(last_instr)
						|| instr_is_ubr(last_instr)
						|| instr_is_interrupt(last_instr));

		instr_t *instr_cpy = instr_clone(drcontext, last_instr);
		instrlist_append(case_bb, instr_cpy);
	}

	return case_bb;
}

static void drbbdup_handle_pre_analysis(void *drcontext, instrlist_t *bb,
		instr_t *strt, void **pre_analysis_data) {

	DR_ASSERT(pre_analysis_data);

	*pre_analysis_data = NULL;

	/**
	 * Trigger pre analysis event.
	 * This useful for user to set up things before analysis
	 */
	if (!opts.functions.pre_analyse_bb)
		return;

	DR_ASSERT(instr_get_note(strt) == (void * ) DRBBDUP_LABEL_NORMAL);
	strt = instr_get_next(strt);

	instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);
	/** Let the user analyse the BB and set case info **/
	opts.functions.pre_analyse_bb(drcontext, case_bb, opts.functions.user_data,
			pre_analysis_data);

	instrlist_clear_and_destroy(drcontext, case_bb);
}

static void drbbdup_analyse_one_bb(void *drcontext, instrlist_t *bb,
		instr_t *strt, const drbbdup_case_t *case_info, void *pre_analysis_data,
		void **analysis_data) {

	instr_t *strt_check = NULL;

	DR_ASSERT(instr_get_note(strt) == (void * )DRBBDUP_LABEL_NORMAL);
	strt = instr_get_next(strt);

	/**
	 * Extract the code of the case.
	 * Create separate lists to make it simple for the user
	 **/
	instrlist_t *case_bb = drbbdup_derive_case_bb(drcontext, bb, &strt);

	*analysis_data = NULL;
	/** Let the user analyse the BB and set case info **/
	opts.functions.analyse_bb(drcontext, case_bb, case_info->condition_val,
			opts.functions.user_data, pre_analysis_data, analysis_data);
	instrlist_clear_and_destroy(drcontext, case_bb);

	strt_check = drbbdup_forward_next(drcontext, bb, strt, NULL);
	DR_ASSERT(strt_check == strt); // should point to same instr.
}

static void drbbdup_analyse_bbs(void *drcontext, drbbdup_per_thread *pt,
		instrlist_t *bb, instr_t *strt, drbbdup_manager_t *manager) {

	/** Instrument default **/
	drbbdup_case_t *case_info = &(manager->default_case);
	DR_ASSERT(case_info);
	DR_ASSERT(case_info->is_defined);

	drbbdup_handle_pre_analysis(drcontext, bb, strt, &(pt->pre_analysis_data));

	/* Handle default case */
	drbbdup_analyse_one_bb(drcontext, bb, strt, case_info,
			pt->pre_analysis_data, &(pt->instrum_infos[0]));

	/** Instrument cases **/
	for (int i = 0; i < opts.fp_settings.dup_limit; i++) {

		case_info = &(manager->cases[i]);
		if (case_info->is_defined) {
			drbbdup_analyse_one_bb(drcontext, bb, strt, case_info,
					pt->pre_analysis_data, &(pt->instrum_infos[i + 1]));
		}
	}
}

static dr_emit_flags_t drbbdup_analyse_phase(void *drcontext, void *tag,
		instrlist_t *bb, bool for_trace, bool translating, void *user_data) {

	drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
			drcontext, tls_idx);

	app_pc pc = instr_get_app_pc(instrlist_first_app(bb));

	/* Fetch hashtable */
	dr_rwlock_read_lock(rw_lock);
	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, pc);

	if (manager == NULL || manager->manager_opts.is_reverted) {
		dr_rwlock_read_unlock(rw_lock);
		return DR_EMIT_DEFAULT;
	}

	/* Analyse basic block based on case data. */
	drbbdup_analyse_bbs(drcontext, pt, bb, instrlist_first(bb), manager);

	dr_rwlock_read_unlock(rw_lock);
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
		instr_t *where, const drbbdup_manager_t *manager) {

	/** When control reached a bb, we need to restore from the JMP **/
	if (!manager->is_eflag_dead) {

		drbbdup_restore_register(drcontext, bb, where, 2, DRBBDUP_SCRATCH);
		dr_restore_arith_flags_from_xax(drcontext, bb, where);
	}

	if (!manager->is_xax_dead)
		drbbdup_restore_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH);
}

static uint drbbdup_get_hitcount_hash(intptr_t bb_id) {

	uint hash = ((uint) bb_id) << 1;
	hash &= (TABLE_SIZE - 1); //
	DR_ASSERT(hash < TABLE_SIZE);
	return hash;
}

static bool include_path_gen(drbbdup_manager_t *manager) {

	bool found = false;
	int i;
	for (i = 0; i < opts.fp_settings.dup_limit; i++) {

		drbbdup_case_t *drbbdup_case = &(manager->cases[i]);

		if (!drbbdup_case->is_defined) {
			found = true;
			break;
		}
	}

	return found;
}

static void drbbdup_insert_encoding(void *drcontext, drbbdup_per_thread *pt,
		app_pc translation_pc, void *tag, instrlist_t *bb, instr_t *where,
		drbbdup_manager_t *manager) {

	instr_t *instr;
	opnd_t opnd;

#ifdef ENABLE_STATS
	drbbdup_stat_clean_bb_exec(drcontext, bb, where);
#endif

	/* Spill register. */
	if (drreg_are_aflags_dead(drcontext, where, &(manager->is_eflag_dead))
			!= DRREG_SUCCESS)
		DR_ASSERT(false);

	if (drreg_is_register_dead(drcontext, DRBBDUP_SCRATCH, where,
			&(manager->is_xax_dead)) != DRREG_SUCCESS)
		DR_ASSERT(false);

	if (!manager->is_xax_dead)
		drbbdup_spill_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH);

	if (!manager->is_eflag_dead) {
		dr_save_arith_flags_to_xax(drcontext, bb, where);
		drbbdup_spill_register(drcontext, bb, where, 2, DRBBDUP_SCRATCH);
		if (!manager->is_xax_dead)
			drbbdup_restore_register(drcontext, bb, where, 1, DRBBDUP_SCRATCH);
	}

	/* Call user function to get comparison */
	opts.functions.get_comparator(drcontext, bb, where,
			opts.functions.user_data, pt->pre_analysis_data);

	/* Restore unreserved registers */
	drreg_restore_all_now(drcontext, bb, where);

	opnd_t scratch_reg_opnd = opnd_create_reg(DRBBDUP_SCRATCH);

//	if (manager->manager_opts.enable_revert_check) {
//
//		DR_ASSERT(!manager->manager_opts.is_reverted);
//
//		opnd_t revert_table_opnd = drbbdup_get_tls_raw_slot_opnd(
//		DRBBDUP_REVERT_TABLE_SLOT);
//
//		instr = INSTR_CREATE_mov_ld(drcontext, scratch_reg_opnd,
//				revert_table_opnd);
//		instrlist_meta_preinsert(bb, where, instr);
//
//		uint hash = drbbdup_get_hitcount_hash((intptr_t) translation_pc);
//		opnd_t revert_count_opnd = OPND_CREATE_MEM16(DRBBDUP_SCRATCH,
//				hash * sizeof(ushort));
//		opnd = opnd_create_immed_uint(1, OPSZ_2);
//		instr = INSTR_CREATE_add(drcontext, revert_count_opnd, opnd);
//		instrlist_meta_preinsert(bb, where, instr);
//
//		instr = INSTR_CREATE_mov_imm(drcontext, scratch_reg_opnd,
//				opnd_create_immed_int((intptr_t) tag, OPSZ_PTR));
//		instrlist_meta_preinsert(bb, where, instr);
//
//		instr = INSTR_CREATE_jcc(drcontext, OP_jo,
//				opnd_create_pc(fp_stop_revert_cache_pc));
//		instrlist_meta_preinsert(bb, where, instr);
//	}

	/**
	 * Load the comparator value to register.
	 * We could compare directly via addressable mem ref, but this will
	 * destroy micro-fusing (mem and immed) !
	 */
	opnd = drbbdup_get_comparator_opnd();
	instr = INSTR_CREATE_mov_ld(drcontext, scratch_reg_opnd, opnd);
	instrlist_meta_preinsert(bb, where, instr);
}

static void drbbdup_insert_chain(void *drcontext, instrlist_t *bb,
		instr_t *where, drbbdup_manager_t *manager, instr_t *next_label,
		drbbdup_case_t *current_case) {

	instr_t *instr;
	opnd_t opnd;

	opnd = opnd_create_immed_uint((uintptr_t) current_case->condition_val,
			opnd_size_from_bytes(sizeof(current_case->condition_val)));
	instr = INSTR_CREATE_cmp(drcontext, opnd_create_reg(DRBBDUP_SCRATCH), opnd);
	instrlist_meta_preinsert(bb, where, instr);

	instr = INSTR_CREATE_jcc(drcontext, OP_jnz, opnd_create_instr(next_label));
	instrlist_meta_preinsert(bb, where, instr);

	drbbdup_insert_landing_restoration(drcontext, bb, where, manager);
}

static void drbbdup_insert_chain_end(void *drcontext, app_pc translation_pc,
		void *tag, instrlist_t *bb, instr_t *where, drbbdup_manager_t *manager) {

	instr_t *instr;
	opnd_t opnd;

	instr_t *done_label = INSTR_CREATE_label(drcontext);
	opnd_t mask_opnd = opnd_create_reg(DRBBDUP_SCRATCH);

	if (manager->manager_opts.enable_dynamic_fp) {
		if (include_path_gen(manager)) {

			drbbdup_case_t *default_info = &(manager->default_case);
			DR_ASSERT(default_info != NULL);
			DR_ASSERT(default_info->is_defined);

			/* If conditional is not defined, perform default check */
			opnd = opnd_create_immed_uint(
					(uintptr_t) default_info->condition_val,
					opnd_size_from_bytes(sizeof(default_info->condition_val)));
			instr = INSTR_CREATE_cmp(drcontext, mask_opnd, opnd);
			instrlist_meta_preinsert(bb, where, instr);

			instr = INSTR_CREATE_jcc(drcontext, OP_jz,
					opnd_create_instr(done_label));
			instrlist_meta_preinsert(bb, where, instr);

			if (manager->manager_opts.enable_pop_threshold) {

				instr = INSTR_CREATE_popcnt(drcontext, mask_opnd, mask_opnd);
				instrlist_meta_preinsert(bb, where, instr);

				opnd = opnd_create_immed_uint(
						(uintptr_t) manager->manager_opts.max_pop_threshold,
						OPSZ_PTR);
				instr = INSTR_CREATE_cmp(drcontext, mask_opnd, opnd);
				instrlist_meta_preinsert(bb, where, instr);

#ifdef ENABLE_STATS

				instr_t* popcnt_label = INSTR_CREATE_label(drcontext);

				instr = INSTR_CREATE_jcc(drcontext, OP_jle,
						opnd_create_instr(popcnt_label));
				instrlist_meta_preinsert(bb, where, instr);

				drbbdup_stat_popcnt_entry(drcontext, bb, where);

				instr = INSTR_CREATE_jmp(drcontext,
						opnd_create_instr(done_label));
				instrlist_meta_preinsert(bb, where, instr);


				instrlist_meta_preinsert(bb, where, popcnt_label);

#else
				instr = INSTR_CREATE_jcc(drcontext, OP_jg,
						opnd_create_instr(done_label));
				instrlist_meta_preinsert(bb, where, instr);
#endif
			}

			if (opts.fp_settings.hit_threshold > 0) {

				opnd_t hit_table_opnd;
				hit_table_opnd = drbbdup_get_tls_raw_slot_opnd(
				DRBBDUP_HIT_TABLE_SLOT);

				/* Load the hit counter table */
				instr = INSTR_CREATE_mov_ld(drcontext, mask_opnd,
						hit_table_opnd);
				instrlist_meta_preinsert(bb, where, instr);

				uint hash = drbbdup_get_hitcount_hash(
						(intptr_t) translation_pc);
				opnd_t hit_count_opnd = OPND_CREATE_MEM16(DRBBDUP_SCRATCH,
						hash * sizeof(ushort));
				opnd = opnd_create_immed_uint(1, OPSZ_2);
				instr = INSTR_CREATE_sub(drcontext, hit_count_opnd, opnd);
				instrlist_meta_preinsert(bb, where, instr);

				/* Insert new case handling here */
				instr = INSTR_CREATE_mov_imm(drcontext, mask_opnd,
						opnd_create_immed_int((intptr_t) tag, OPSZ_PTR));
				instrlist_meta_preinsert(bb, where, instr);

				opnd = opnd_create_pc(fp_new_case_cache_pc);
				instr = INSTR_CREATE_jcc(drcontext, OP_jz, opnd);
				instrlist_meta_preinsert(bb, where, instr);

			} else {

				/* Insert new case handling here */
				instr = INSTR_CREATE_mov_imm(drcontext, mask_opnd,
						opnd_create_immed_int((intptr_t) tag, OPSZ_PTR));
				instrlist_meta_preinsert(bb, where, instr);

				opnd = opnd_create_pc(fp_new_case_cache_pc);
				instr = INSTR_CREATE_jmp(drcontext, opnd);
				instrlist_meta_preinsert(bb, where, instr);
			}
		}

#ifdef ENABLE_STATS
		else {

			drbbdup_stat_clean_bail_entry(drcontext, bb, where);
		}
#endif
	}

	instrlist_meta_preinsert(bb, where, done_label);

	drbbdup_insert_landing_restoration(drcontext, bb, where, manager);

}

static dr_emit_flags_t drbbdup_link_phase(void *drcontext, void *tag,
		instrlist_t *bb, instr_t *instr, bool for_trace, bool translating,
		void *user_data) {

	drbbdup_case_t *drbbdup_case = NULL;
	drbbdup_case_t *analysis_data = NULL;

	drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
			drcontext, tls_idx);

	/* Fetch case manager */
	app_pc pc = instr_get_app_pc(instrlist_first_app(bb));

	dr_rwlock_read_lock(rw_lock);
	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, pc);

	if (manager == NULL || manager->manager_opts.is_reverted) {
		/** No fast path code wanted! Instrument normally and return! **/

		dr_rwlock_read_unlock(rw_lock);
		opts.functions.nan_instrument_bb(drcontext, bb, instr,
				opts.functions.user_data);
		return DR_EMIT_DEFAULT;
	}

	instr_t *next_instr = instr_get_next(instr);

	if (drmgr_is_first_instr(drcontext, instr)) {

		/* Set up entry point to fast paths */
		DR_ASSERT(
				instr_is_label(instr)
						&& instr_get_note(instr)
								== (void * )DRBBDUP_LABEL_NORMAL);

		/* Start with the first case */
		pt->case_index = 1;
		drbbdup_case = &(manager->cases[pt->case_index - 1]);

		/* Insert jumps prior entry label of  block instance */
		drbbdup_insert_encoding(drcontext, pt, pc, tag, bb, instr, manager);

		drbbdup_label_t label_info;
		instr_t * next_label = drbbdup_forward_next(drcontext, bb, next_instr,
				&label_info);
		DR_ASSERT(next_label);
		DR_ASSERT(label_info == DRBBDUP_LABEL_NORMAL);

		drbbdup_insert_chain(drcontext, bb, next_instr, manager, next_label,
				drbbdup_case);

#ifdef ENABLE_STATS
		drbbdup_stat_clean_case_entry(drcontext, bb, next_instr,
				pt->case_index);
#endif

	} else {

		drbbdup_label_t label_info;
		bool result = drbbdup_is_at_end(instr, &label_info);

		if (result && label_info == DRBBDUP_LABEL_NORMAL) {

			drbbdup_label_t label_info;
			instr_t * next_label = drbbdup_forward_next(drcontext, bb,
					next_instr, &label_info);

			if (label_info == DRBBDUP_LABEL_EXIT) {

				pt->case_index = 0;

				drbbdup_insert_chain_end(drcontext, pc, tag, bb, next_instr,
						manager);
			} else {

				/* We have reached the start of a new case */
				bool found = false;
				int i;
				for (i = pt->case_index + 1;
						i < (opts.fp_settings.dup_limit + 1); i++) {

					drbbdup_case = &(manager->cases[i - 1]);

					if (drbbdup_case->is_defined) {
						found = true;
						break;
					}
				}

				DR_ASSERT(found);
				DR_ASSERT(pt->case_index + 1 == i);
				pt->case_index = i;

				/* Insert start of chain */
				drbbdup_insert_chain(drcontext, bb, next_instr, manager,
						next_label, drbbdup_case);
			}

#ifdef ENABLE_STATS
			drbbdup_stat_clean_case_entry(drcontext, bb, next_instr,
					pt->case_index);
#endif

		} else if (result && label_info == DRBBDUP_LABEL_EXIT) {

			DR_ASSERT(pt->case_index == 0);

			instr_t *last = instrlist_last_app(bb);
			if (instr_is_syscall(last) || instr_is_cti(last)
					|| instr_is_ubr(last) || instr_is_interrupt(last)) {

				drbbdup_case = &(manager->default_case);
				analysis_data = pt->instrum_infos[pt->case_index];
				opts.functions.instrument_bb(drcontext, bb, last, instr,
						drbbdup_case->condition_val, opts.functions.user_data,
						pt->pre_analysis_data, analysis_data);
			}

			drreg_restore_all_now(drcontext, bb, instr);

			/* Set to -1 to always trigger default behaviour. */
			pt->case_index = -1;

		} else {

			/**
			 * Check if we need to restore all spilled register.
			 * This is done when we encounter a jump to exit
			 */
			if (instr_is_cti(instr) && instr_get_next(instr) != NULL) {

				result = drbbdup_is_at_end(instr_get_next(instr), &label_info);

				/* Include restoration before jmp instr */
				if (result && (label_info == DRBBDUP_LABEL_NORMAL)) {

					instr_t *last = instrlist_last_app(bb);
					if (instr_is_syscall(last) || instr_is_cti(last)
							|| instr_is_ubr(last) || instr_is_interrupt(last)) {

						drbbdup_case = &(manager->cases[pt->case_index - 1]);
						DR_ASSERT(drbbdup_case->is_defined);
						analysis_data = pt->instrum_infos[pt->case_index];
						opts.functions.instrument_bb(drcontext, bb, last, instr,
								drbbdup_case->condition_val,
								opts.functions.user_data, pt->pre_analysis_data,
								analysis_data);
					}

					drreg_restore_all_now(drcontext, bb, instr);

					/* Don't bother instrumenting jmp exists of fast paths */
					dr_rwlock_read_unlock(rw_lock);
					return DR_EMIT_DEFAULT;
				}
			}

			if (instr_is_app(instr)) {

				if (pt->case_index == -1) {

					DR_ASSERT(
							instr_is_syscall(instr) || instr_is_cti(instr)
									|| instr_is_ubr(instr)
									|| instr_is_interrupt(instr));
				} else {

					if (pt->case_index == 0) {
						/* If zero, use default */
						drbbdup_case = &(manager->default_case);
					} else {
						/* Otherwise use special case */
						/* We perform -1 on index to take into account default case. */
						drbbdup_case = &(manager->cases[pt->case_index - 1]);
					}
					DR_ASSERT(drbbdup_case->is_defined);

					analysis_data = pt->instrum_infos[pt->case_index];

					opts.functions.instrument_bb(drcontext, bb, instr, instr,
							drbbdup_case->condition_val,
							opts.functions.user_data, pt->pre_analysis_data,
							analysis_data);
				}
			}
		}
	}
	dr_rwlock_read_unlock(rw_lock);

	if (drmgr_is_last_instr(drcontext, instr)) {

		if (opts.functions.destroy_analysis) {
			int i;
			for (i = 0; i < (opts.fp_settings.dup_limit + 1); i++) {

				if (pt->instrum_infos[i] != NULL) {
					opts.functions.destroy_analysis(drcontext,
							opts.functions.user_data, pt->pre_analysis_data,
							pt->instrum_infos[i]);
					pt->instrum_infos[i] = NULL;
				}
			}
		}

		if (opts.functions.destroy_pre_analysis) {

			if (pt->pre_analysis_data) {
				opts.functions.destroy_pre_analysis(drcontext,
						opts.functions.user_data, pt->pre_analysis_data);
				pt->pre_analysis_data = NULL;
			}
		}
	}

	return DR_EMIT_DEFAULT;
}

/************************************************************************
 * New Case HANDING
 */

static void drbbdup_prepare_redirect(dr_mcontext_t *mcontext,
		drbbdup_manager_t *manager, app_pc bb_pc) {

	if (!manager->is_eflag_dead) {
		// Eflag restoration is taken from drreg. Should move it upon release.
		reg_t newval = mcontext->xflags;
		reg_t val;
		uint sahf;
		val = drbbdup_get_spilled(DRBBDUP_FLAG_REG_SLOT);
		sahf = (val & 0xff00) >> 8;
		newval &= ~(EFLAGS_ARITH);
		newval |= sahf;
		if (TEST(1, val)) /* seto */
			newval |= EFLAGS_OF;
		mcontext->xflags = newval;
	}
	if (!manager->is_xax_dead)
		reg_set_value(DRBBDUP_SCRATCH, mcontext,
				drbbdup_get_spilled(DRBBDUP_XAX_REG_SLOT));
	mcontext->pc = bb_pc;

}

static void drbbdup_handle_new_case() {

#ifdef ENABLE_STATS
	drbbdup_stat_inc_gen();
#endif

	void *drcontext = dr_get_current_drcontext();

	/* Must use DR_MC_ALL due to dr_redirect_execution */
	dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
	dr_get_mcontext(drcontext, &mcontext);

	void *tag = (void *) reg_get_value(DRBBDUP_SCRATCH, &mcontext);

	instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
	instr_t *instr = instrlist_first_app(ilist);
	app_pc bb_pc = instr_get_app_pc(instr);
	instrlist_clear_and_destroy(drcontext, ilist);

	/* Get the missing case */
	reg_t conditional_val = (reg_t) drbbdup_get_comparator();

	/* Look up case manager */
	dr_rwlock_write_lock(rw_lock);

	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, bb_pc);

	if (!manager)
		DR_ASSERT_MSG(false, "Can't find manager!\n");

	/* Find an undefined case, and set it up for the new conditional. */

	/* Check whether the default case is actually the missing case. */

	int i;
	for (i = 0; i < opts.fp_settings.dup_limit; i++) {

		if (!(manager->cases[i].is_defined)) {

			manager->cases[i].is_defined = true;
			manager->cases[i].condition_val =
					(unsigned int) (uintptr_t) conditional_val;
			break;
		}
	}

	manager->manager_opts.enable_revert_check = false;

	drbbdup_prepare_redirect(&mcontext, manager, bb_pc);

	dr_rwlock_write_unlock(rw_lock);

	/* Refresh hit counter*/
	drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
			drcontext, tls_idx);

	if (opts.fp_settings.hit_threshold > 0) {
		uint hash = drbbdup_get_hitcount_hash((intptr_t) bb_pc);
		DR_ASSERT(pt->hit_counts[hash] == 0);
		pt->hit_counts[hash] = opts.fp_settings.hit_threshold;
	}

	LOG(drcontext, DR_LOG_ALL, 2, "%s Found new taint case! I am about to flush for %p\n",
			__FUNCTION__, bb_pc);

	bool succ = dr_delete_shared_fragment(tag);
	DR_ASSERT(succ);

	dr_redirect_execution(&mcontext);
}

static void drbbdup_handle_revert() {

#ifdef ENABLE_STATS
	drbbdup_stat_inc_revert();
#endif

	void *drcontext = dr_get_current_drcontext();

	/* Must use DR_MC_ALL due to dr_redirect_execution */
	dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
	dr_get_mcontext(drcontext, &mcontext);

	void *tag = (void *) reg_get_value(DRBBDUP_SCRATCH, &mcontext);
	instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
	instr_t *instr = instrlist_first_app(ilist);
	app_pc bb_pc = instr_get_app_pc(instr);
	instrlist_clear_and_destroy(drcontext, ilist);

	bool already_reverted = false;

	/* Look up case manager */
	dr_rwlock_write_lock(rw_lock);

	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, bb_pc);

	if (!manager)
		DR_ASSERT_MSG(false, "Can't find manager!\n");

	already_reverted = !manager->manager_opts.enable_revert_check;

	if (!already_reverted) {
		DR_ASSERT(!manager->manager_opts.is_reverted);
		DR_ASSERT(manager->manager_opts.enable_revert_check);
		manager->manager_opts.is_reverted = true;
		manager->manager_opts.enable_revert_check = false;

	} else {
		DR_ASSERT(!manager->manager_opts.enable_revert_check);
	}

	drbbdup_prepare_redirect(&mcontext, manager, bb_pc);

	dr_rwlock_write_unlock(rw_lock);

	if (!already_reverted) {
		drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
				drcontext, tls_idx);

		LOG(drcontext, DR_LOG_ALL, 2, "%s Reverting for basic block %p\n",
				__FUNCTION__, bb_pc);

		uint hash = drbbdup_get_hitcount_hash((intptr_t) bb_pc);
		DR_ASSERT(pt->revert_counts[hash] == 0);
		pt->revert_counts[hash] = opts.fp_settings.revert_threshold;

		bool succ = dr_delete_shared_fragment(tag);
		DR_ASSERT(succ);
	}

	dr_redirect_execution(&mcontext);
}

static void drbbdup_handle_stop_revert() {

#ifdef ENABLE_STATS
	drbbdup_stat_inc_stop_revert();
#endif

	void *drcontext = dr_get_current_drcontext();

	/* Must use DR_MC_ALL due to dr_redirect_execution */
	dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
	dr_get_mcontext(drcontext, &mcontext);

	void *tag = (void *) reg_get_value(DRBBDUP_SCRATCH, &mcontext);

	instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
	instr_t *instr = instrlist_first_app(ilist);
	app_pc bb_pc = instr_get_app_pc(instr);
	instrlist_clear_and_destroy(drcontext, ilist);

	bool already_reverted = false;

	/* Look up case manager */
	dr_rwlock_write_lock(rw_lock);

	drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
			&case_manager_table, bb_pc);

	if (!manager)
		DR_ASSERT_MSG(false, "Can't find manager!\n");

	already_reverted = !manager->manager_opts.enable_revert_check;

	if (!already_reverted) {
		DR_ASSERT(manager->manager_opts.enable_revert_check);
		manager->manager_opts.enable_revert_check = false;
	}

	drbbdup_prepare_redirect(&mcontext, manager, bb_pc);

	dr_rwlock_write_unlock(rw_lock);

	if (!already_reverted) {
		drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
				drcontext, tls_idx);

		uint hash = drbbdup_get_hitcount_hash((intptr_t) bb_pc);
		pt->revert_counts[hash] = opts.fp_settings.revert_threshold;

		bool succ = dr_delete_shared_fragment(tag);
		DR_ASSERT(succ);
	}

	dr_redirect_execution(&mcontext);
}

static app_pc init_fp_cache(void (*clean_call_func)()) {

	app_pc cache_pc;
	instrlist_t *ilist;
	size_t size;

	void *drcontext = dr_get_current_drcontext();

	ilist = instrlist_create(drcontext);

	dr_insert_clean_call(drcontext, ilist, NULL, clean_call_func,
	false, 0);

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

// Change the permission Read-Write-Execute permissions.
// In particular, we do not need to write the the private cache
	dr_memory_protect(cache_pc, size, DR_MEMPROT_READ | DR_MEMPROT_EXEC);

	return cache_pc;
}

static void destroy_fp_cache(app_pc cache_pc) {

	dr_nonheap_free(cache_pc, dr_page_size());
}

///******************************************************************
// * Frag Deletion
// */
//
//static void deleted_frag(void *drcontext, void *tag) {
//
//    if (drcontext == NULL)
//        return;
//
//    drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
//            drcontext, tls_idx);
//
//    app_pc bb_pc = dr_fragment_app_pc(tag);
//
//    drbbdup_manager_t *manager = (drbbdup_manager_t *) hashtable_lookup(
//            &(pt->case_manager_table), bb_pc);
//
//    if (manager) {
//
//        dr_fprintf(STDERR, "Found in removal %p\n", bb_pc);
//
////
////        DR_ASSERT(manager->ref_counter > 0);
////        manager->ref_counter--;
////
////        if (manager->ref_counter <= 0) {
////            dr_fprintf(STDERR, "Removing %p %d\n", bb_pc, manager->fp_flag);
////
////            bool is_removed = hashtable_remove(&(pt->case_manager_table),
////                    bb_pc);
////            DR_ASSERT(is_removed);
////        }
//    }
//}

/************************************************************************
 * INIT
 */

DR_EXPORT drbbdup_status_t drbbdup_register_case_value(void *drbbdup_ctx,
		uint case_val) {

	drbbdup_manager_t *manager = (drbbdup_manager_t *) drbbdup_ctx;

	int i;
	for (i = 0; i < opts.fp_settings.dup_limit; i++) {
		drbbdup_case_t *dup_case = &(manager->cases[i]);
		if (!dup_case->is_defined) {

			dup_case->is_defined = true;
			dup_case->condition_val = case_val;
			return DRBBDUP_SUCCESS;
		}
	}

	return DRBBDUP_ERROR;
}

DR_EXPORT drbbdup_status_t drbbdup_unregister_case_value(void *drbbdup_ctx,
		uint case_val) {

	drbbdup_manager_t *manager = (drbbdup_manager_t *) drbbdup_ctx;

	int i;
	for (i = 0; i < opts.fp_settings.dup_limit; i++) {

		drbbdup_case_t *dup_case = &(manager->cases[i]);
		if (dup_case->is_defined && dup_case->condition_val == case_val) {

			dup_case->is_defined = false;
			return DRBBDUP_SUCCESS;
		}
	}

	return DRBBDUP_ERROR;
}

static void drbbdup_destroy_manager(void *manager_opaque) {

	drbbdup_manager_t *manager = (drbbdup_manager_t *) manager_opaque;
	dr_global_free(manager->cases,
			sizeof(drbbdup_case_t) * opts.fp_settings.dup_limit);
	dr_global_free(manager, sizeof(drbbdup_manager_t));
}

static void drbbdup_thread_init(void *drcontext) {

	drbbdup_per_thread *pt = (drbbdup_per_thread *) dr_thread_alloc(drcontext,
			sizeof(*pt));
	pt->case_index = 0;

	pt->pre_analysis_data = NULL;
	pt->instrum_infos = dr_global_alloc(
			sizeof(void *) * (opts.fp_settings.dup_limit + 1));
	memset(pt->instrum_infos, 0,
			sizeof(void *) * (opts.fp_settings.dup_limit + 1));

	for (int i = 0; i < TABLE_SIZE; i++) {
		pt->hit_counts[i] = opts.fp_settings.hit_threshold;
	}

	for (int i = 0; i < TABLE_SIZE; i++) {
		pt->revert_counts[i] = opts.fp_settings.revert_threshold;
	}

	byte *addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
			+ (DRBBDUP_HIT_TABLE_SLOT * (sizeof(void *))));
	void **addr_hitcount = (void **) addr;
	*addr_hitcount = pt->hit_counts;

	addr = (dr_get_dr_segment_base(tls_raw_reg) + tls_raw_base
			+ (DRBBDUP_REVERT_TABLE_SLOT * (sizeof(void *))));
	void **addr_revertcount = (void **) addr;
	*addr_revertcount = pt->revert_counts;

	drmgr_set_tls_field(drcontext, tls_idx, (void *) pt);
}

static void drbbdup_thread_exit(void *drcontext) {

	drbbdup_per_thread *pt = (drbbdup_per_thread *) drmgr_get_tls_field(
			drcontext, tls_idx);

	dr_global_free(pt->instrum_infos,
			sizeof(void *) * (opts.fp_settings.dup_limit + 1));
	dr_thread_free(drcontext, pt, sizeof(*pt));
}

static void drbbdup_set_options(drbbdup_options_t *ops_in,
		drbbdup_fp_settings_t *fp_settings_in) {

	/* Perform checks */
	DR_ASSERT(ops_in);
	DR_ASSERT(ops_in->create_manager);
	DR_ASSERT(ops_in->get_comparator);
	DR_ASSERT(ops_in->analyse_bb);
	DR_ASSERT(ops_in->instrument_bb);
	DR_ASSERT(ops_in->nan_instrument_bb);

	if (fp_settings_in == NULL) {
		/* Set default values for fp settings */
		opts.fp_settings.dup_limit = 3;
		opts.fp_settings.required_size = 0;
		opts.fp_settings.hit_threshold = 3500;
		opts.fp_settings.enable_revert = true;
		opts.fp_settings.revert_threshold = 5000;

	} else {
		memcpy(&(opts.fp_settings), fp_settings_in,
				sizeof(drbbdup_fp_settings_t));
	}

	DR_ASSERT(opts.fp_settings.dup_limit > 0);
	DR_ASSERT(opts.fp_settings.revert_threshold < 30000);

	memcpy(&(opts.functions), ops_in, sizeof(drbbdup_options_t));
}

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_init_ex(drbbdup_options_t *ops_in,
		drbbdup_fp_settings_t *fp_settings,
		drmgr_priority_t *bb_instrum_priority) {

	if (drbbdup_ref_count == 0) {

		drbbdup_set_options(ops_in, fp_settings);

		drreg_options_t drreg_ops = { sizeof(drreg_ops), 5, false, NULL,
		true };

		drmgr_priority_t priority = { sizeof(drmgr_priority_t), "DRBBDUP_DUPS",
		NULL, NULL, -7500 };

		if (!drmgr_register_bb_app2app_event(drbbdup_duplicate_phase,
				&priority))
			DR_ASSERT(false);

		if (!drmgr_register_bb_instrumentation_ex_event(NULL,
				drbbdup_analyse_phase, drbbdup_link_phase, NULL,
				bb_instrum_priority) || drreg_init(&drreg_ops) != DRREG_SUCCESS)
			DR_ASSERT(false);

		if (!drmgr_register_thread_init_event(drbbdup_thread_init)
				|| !drmgr_register_thread_exit_event(drbbdup_thread_exit))
			return DRBBDUP_ERROR;

//        dr_register_delete_event(deleted_frag);

		tls_idx = drmgr_register_tls_field();
		if (tls_idx == -1)
			return DRBBDUP_ERROR;

		dr_raw_tls_calloc(&(tls_raw_reg), &(tls_raw_base), 6, 0);

		fp_new_case_cache_pc = init_fp_cache(drbbdup_handle_new_case);
		fp_revert_cache_pc = init_fp_cache(drbbdup_handle_revert);
		fp_stop_revert_cache_pc = init_fp_cache(drbbdup_handle_stop_revert);

		/**
		 * We initialise the hash table that keeps track of defined cases per
		 * basic block.
		 */
		hashtable_init_ex(&case_manager_table, HASH_BIT_TABLE, HASH_INTPTR,
		false, false, drbbdup_destroy_manager, NULL, NULL);

		rw_lock = dr_rwlock_create();

#ifdef ENABLE_STATS

		time_file = dr_open_file(TIME_FILE, DR_FILE_WRITE_OVERWRITE);

		case_num = dr_global_alloc(
				sizeof(unsigned long) * (opts.fp_settings.dup_limit + 1));
		memset(case_num, 0,
				sizeof(unsigned long) * (opts.fp_settings.dup_limit + 1));

		stat_mutex = dr_mutex_create();

		dr_create_client_thread(sample_thread, NULL);
#endif

	}

	drbbdup_ref_count++;
	return DRBBDUP_SUCCESS;
}

DR_EXPORT bool drbbdup_is_last_instr(instrlist_t *bb, instr_t *instr) {

	instr_t *last = instrlist_last(bb);
	if (instr_is_syscall(last) || instr_is_cti(last) || instr_is_ubr(last)
			|| instr_is_interrupt(last)) {
		return instr_same(instr, last);
	}

	while (instr) {

		instr = instr_get_next(instr);

		if (instr_is_app(instr)) {

			if (instr_is_cti(instr)) {
				instr_t *next_instr = instr_get_next(instr);

				if (next_instr != NULL && instr_is_label(next_instr)
						&& instr_get_note(next_instr)
								== (void *) DRBBDUP_LABEL_NORMAL) {
					return true;
				}
			}

			return false;

		} else {
			if (drbbdup_is_at_end(instr, NULL))
				return true;
		}
	}

	return false;
}

DR_EXPORT drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in,
		drmgr_priority_t *bb_instrum_priority) {

	return drbbdup_init_ex(ops_in, NULL, bb_instrum_priority);
}

DR_EXPORT drbbdup_status_t drbbdup_exit(void) {

	DR_ASSERT(drbbdup_ref_count > 0);
	drbbdup_ref_count--;

	if (drbbdup_ref_count == 0) {

		DR_ASSERT(fp_new_case_cache_pc);
		destroy_fp_cache(fp_new_case_cache_pc);
		DR_ASSERT(fp_revert_cache_pc);
		destroy_fp_cache(fp_revert_cache_pc);
		DR_ASSERT(fp_stop_revert_cache_pc);
		destroy_fp_cache(fp_stop_revert_cache_pc);

		drmgr_unregister_bb_app2app_event(drbbdup_duplicate_phase);

		drmgr_unregister_bb_instrumentation_ex_event(NULL,
				drbbdup_analyse_phase, drbbdup_link_phase, NULL);

		if (!drmgr_unregister_thread_init_event(drbbdup_thread_init)
				|| !drmgr_unregister_thread_exit_event(drbbdup_thread_exit))
			return DRBBDUP_ERROR;

		dr_raw_tls_cfree(tls_raw_base, 6);
		drmgr_unregister_tls_field(tls_idx);
//        dr_unregister_delete_event(deleted_frag);
		drreg_exit();

		hashtable_delete(&case_manager_table);
		dr_rwlock_destroy(rw_lock);

#ifdef ENABLE_STATS
		drbbdup_stat_print_stats();

		dr_mutex_destroy(stat_mutex);
		dr_global_free(case_num,
				sizeof(unsigned long) * (opts.fp_settings.dup_limit + 1));

		dr_close_file(time_file);

#endif
	}
	return DRBBDUP_SUCCESS;
}

/***********************************************************************************
 * STAT Functions
 */

#ifdef ENABLE_STATS

/**
 * Clean Calls for tracking. I keep things simple and use clean calls.
 *
 * Of course, these clean calls are not executed in release.
 */

static void drbbdup_stat_inc_bb() {

	dr_mutex_lock(stat_mutex);
	total_bb++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_inc_instrum_bb() {

	dr_mutex_lock(stat_mutex);
	bb_instrumented++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_inc_non_applicable() {

	dr_mutex_lock(stat_mutex);
	non_applicable++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_no_fp() {

	dr_mutex_lock(stat_mutex);
	no_fp++;
	dr_mutex_unlock(stat_mutex);

}

static void drbbdup_stat_inc_gen() {

	dr_mutex_lock(stat_mutex);
	gen_num++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_inc_revert() {

	dr_mutex_lock(stat_mutex);
	revert_num++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_inc_stop_revert() {

	dr_mutex_lock(stat_mutex);
	stop_revert_num++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_inc_bb_size(uint size) {

	dr_mutex_lock(stat_mutex);
	total_size += size;
	dr_mutex_unlock(stat_mutex);
}

static void clean_call_case_entry(int i) {
	DR_ASSERT(i >= 0 && i < opts.fp_settings.dup_limit + 1);

	dr_mutex_lock(stat_mutex);
	case_num[i]++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_clean_case_entry(void *drcontext, instrlist_t *bb,
		instr_t *where, int case_index) {

	dr_insert_clean_call(drcontext, bb, where, clean_call_case_entry, false, 1,
			OPND_CREATE_INTPTR(case_index));
}

static void clean_call_bail_entry() {

	dr_mutex_lock(stat_mutex);
	total_bails++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_clean_bail_entry(void *drcontext, instrlist_t *bb,
		instr_t *where) {

	dr_insert_clean_call(drcontext, bb, where, clean_call_bail_entry, false, 0);
}

static void clean_call_popcnt_entry() {

	dr_mutex_lock(stat_mutex);
	total_popcnt++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_popcnt_entry(void *drcontext, instrlist_t *bb,
		instr_t *where) {

	dr_insert_clean_call(drcontext, bb, where, clean_call_popcnt_entry, false, 0);
}

static void clean_call_bb_execc() {

	dr_mutex_lock(stat_mutex);
	total_exec++;
	dr_mutex_unlock(stat_mutex);
}

static void drbbdup_stat_clean_bb_exec(void *drcontext, instrlist_t *bb,
		instr_t *where) {

	dr_insert_clean_call(drcontext, bb, where, clean_call_bb_execc, false, 0);
}

static void drbbdup_stat_print_stats() {

	dr_fprintf(STDERR, "---------------------------\n");

	dr_fprintf(STDERR, "Total BB: %lu\n", total_bb);
	dr_fprintf(STDERR, "Total Skipped: %lu\n", non_applicable);
	dr_fprintf(STDERR, "Total BB with no Dynamic FP: %lu\n", no_fp);
	dr_fprintf(STDERR, "Number of BB instrumented: %lu\n", bb_instrumented);

	if (bb_instrumented != 0)
	dr_fprintf(STDERR, "Avg BB size: %lu\n\n",
			total_size / bb_instrumented);

	dr_fprintf(STDERR, "Number of fast paths generated (bb): %lu\n", gen_num);
	dr_fprintf(STDERR, "Number of reverts (bb): %lu\n", revert_num);
	dr_fprintf(STDERR, "Number of stop-reverts (bb): %lu\n", stop_revert_num);

	dr_fprintf(STDERR, "Total bb exec: %lu\n", total_exec);
	dr_fprintf(STDERR, "Total bails: %lu\n", total_bails);
	dr_fprintf(STDERR, "Total failed popcnt: %lu\n", total_popcnt);

	for (int i = 0; i < opts.fp_settings.dup_limit + 1; i++)
	dr_fprintf(STDERR, "Case %d: %lu\n", i, case_num[i]);

	dr_fprintf(STDERR, "---------------------------\n");

}

unsigned long sample_count = 0;

void record_sample(void *drcontext, dr_mcontext_t *mcontext) {

	dr_mutex_lock(stat_mutex);

	unsigned long new_fp_taint_num = 0;
	for (int i = 2; i < opts.fp_settings.dup_limit + 1; i++)
	new_fp_taint_num += case_num[i];

	new_fp_taint_num = new_fp_taint_num - prev_full_taint_num;
	unsigned long new_fp_gen = gen_num - prev_fp_gen;

	prev_full_taint_num = 0;
	for (int i = 2; i < opts.fp_settings.dup_limit + 1; i++)
	prev_full_taint_num += case_num[i];

	prev_fp_gen = gen_num;

	dr_fprintf(time_file, "(%lu,%lu) (%lu,%lu)\n", sample_count,
			new_fp_taint_num, sample_count, new_fp_gen);

	sample_count++;
	dr_mutex_unlock(stat_mutex);
}

static void sample_thread(void *arg) {

	dr_set_itimer(ITIMER_REAL, 1000, record_sample);

	while (1) {
		dr_thread_yield();
	}
}

#endif

