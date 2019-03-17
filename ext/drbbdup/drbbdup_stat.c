/*
 * drbbdup_stat.c
 *
 *  Created on: 11 Mar 2019
 *      Author: john
 */

#include "drbbdup_stat.h"

#include "dr_api.h"
#include "drbbdup.h"
#include "drmgr.h"

/** Total number of BB witnessed.**/
unsigned long total_bb = 0;

/** Total number of BBs with fast path generation. **/
unsigned long bb_instrumented = 0;

/** Total size of basic blocks (used for avg). **/
unsigned long total_size = 0;

/** Number of non applicable bbs **/
unsigned long non_applicable = 0;

/** Total number of BB executed with faths paths **/
unsigned long total_exec = 0;

/** Number of fast paths generated (faults triggered) **/
unsigned long gen_num = 0;

/** Number of bails to slow path**/
unsigned long total_bails = 0;

/** Number of case entries **/
unsigned long case_num[NUMBER_OF_DUPS + 1];

/** Number of case entries **/
unsigned long limit_reached;

/*******************************************************
 * Clean Calls for tracking. I keep things simple and use clean calls.
 **/

void drbbdup_stat_inc_bb() {
    total_bb++;
}

void drbbdup_stat_inc_instrum_bb() {
    bb_instrumented++;
}

void drbbdup_stat_inc_non_applicable() {

    non_applicable++;
}

void drbbdup_stat_inc_limit_reached() {

    limit_reached++;
}

void drbbdup_stat_inc_gen() {

    gen_num++;
}

void drbbdup_stat_inc_bb_size(uint size) {

    total_size += size;
}

static void clean_call_case_entry(int i) {
    case_num[i]++;
}

void drbbdup_stat_clean_case_entry(void *drcontext, instrlist_t *bb,
        instr_t *where, int case_index) {

    dr_insert_clean_call(drcontext, bb, where, clean_call_case_entry, false, 1,
    OPND_CREATE_INTPTR(case_index));
}

static void clean_call_bail_entry() {
    total_bails++;
}

void drbbdup_stat_clean_bail_entry(void *drcontext, instrlist_t *bb,
        instr_t *where) {

    dr_insert_clean_call(drcontext, bb, where, clean_call_bail_entry, false, 0);
}

static void clean_call_bb_execc() {
    total_exec++;
}

void drbbdup_stat_clean_bb_exec(void *drcontext, instrlist_t *bb,
        instr_t *where) {

    dr_insert_clean_call(drcontext, bb, where, clean_call_bb_execc, false, 0);
}

void drbbdup_stat_print_stats() {

    dr_fprintf(STDERR, "Total BB: %lu\n", total_bb);
    dr_fprintf(STDERR, "Total Skipped: %lu\n", non_applicable);
    dr_fprintf(STDERR, "Number of BB instrumented: %lu\n", bb_instrumented);
    dr_fprintf(STDERR, "Limit Reached: %lu\n", limit_reached);
    dr_fprintf(STDERR, "Avg BB size: %lu\n\n", total_size / bb_instrumented);
    dr_fprintf(STDERR, "Number of faults: %lu\n", gen_num);
    dr_fprintf(STDERR, "Total bb exec: %lu\n", total_exec);
    dr_fprintf(STDERR, "Total bails: %lu\n", total_bails);

    for (int i = 0; i < NUMBER_OF_DUPS + 1; i++)
        dr_fprintf(STDERR, "Case %d: %lu\n", i, case_num[i]);

}

