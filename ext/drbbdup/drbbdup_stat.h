/*
 * drbbdup_stat.h
 *
 *  Created on: 11 Mar 2019
 *      Author: john
 */

#ifndef EXT_DRBBDUP_DRBBDUP_STAT_H_
#define EXT_DRBBDUP_DRBBDUP_STAT_H_

#include "dr_api.h"
#include "drmgr.h"

// Comment out macro for no stats
#define ENABLE_STATS 1

void drbbdup_stat_inc_bb();

void drbbdup_stat_inc_instrum_bb();

void drbbdup_stat_inc_non_applicable();

void drbbdup_stat_inc_limit_reached();

void drbbdup_stat_inc_gen();

void drbbdup_stat_inc_bb_size(uint size);

void drbbdup_stat_clean_case_entry(void *drcontext, instrlist_t *bb,
        instr_t *where, int case_index);

void drbbdup_stat_clean_bail_entry(void *drcontext, instrlist_t *bb,
        instr_t *where);

void drbbdup_stat_clean_bb_exec(void *drcontext, instrlist_t *bb,
        instr_t *where);

void drbbdup_stat_print_stats();

#endif /* EXT_DRBBDUP_DRBBDUP_STAT_H_ */
