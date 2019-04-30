#ifndef EXT_DRBBDUP_DRBBDUP_H_
#define EXT_DRBBDUP_DRBBDUP_H_

#include "dr_api.h"
#include "drmgr.h"
#include "drvector.h"

/**
 * To change the number of fast paths simply set the following number.
 * I am not sure if I should give the user the option to change this at runtime.
 * Those who really care, can just change and compile Dr. I am a fan of less options!
 */
#define NUMBER_OF_DUPS 3
#define DRBBDUP_CMP_REG DR_REG_XCX

#define ENABLE_DELAY_FP_GEN
#define FP_GEN_THRESHOLD 90

/**
 * @file drbbdup.h
 * @brief Header for DynamoRIO Basic Block Duplication Management Extension
 */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Priorities of drmgr instrumentation passes used by drreg.  Users
 * of drreg can use the name DRMGR_PRIORITY_NAME_DRREG in the
 * drmgr_priority_t.before field or can use these numeric priorities
 * in the drmgr_priority_t.priority field to ensure proper
 * instrumentation pass ordering.
 */
enum {
    /** Priority of drbbdup*/
    DRMGR_PRIORITY_DRBBDUP = -1500,
    /** Priority of drbbdup fault handling event */
    DRMGR_PRIORITY_FAULT_DRBBDUP = -1500,
};

/**
 * TODO
 */
#define DRMGR_PRIORITY_NAME_DRBBDUP "drbbdup"

/**
 * TODO
 */
#define DRMGR_PRIORITY_NAME_FAULT_DRBBDUP "drbbdup_fault"

/**
 * TODO
 */
typedef enum {
    DRBBDUP_SUCCESS, /**< Operation succeeded. */
    DRBBDUP_ERROR, /**< Operation failed. */
} drbbdup_status_t;

/**
 * TODO
 */
typedef struct {

    unsigned int condition_val;
    bool is_defined;
} drbbdup_case_t;

/**
 * TODO
 */
typedef struct {

    drbbdup_case_t default_case;
    drbbdup_case_t cases[NUMBER_OF_DUPS];

    bool is_cmp_reg_dead;
    bool is_eflag_dead;

    bool apply_default;
    bool enable_dynamic_fp;

} drbbdup_manager_t;

/**
 * TODO
 */
typedef bool (*drbbdup_create_default_manager_t)(void *drcontext,
        instrlist_t *bb, drbbdup_manager_t *manager, void *user_data);

/**
 * TODO
 */
typedef void (*drbbdup_pre_analyse_bb_t)(void *drcontext, instrlist_t *bb,
        drbbdup_manager_t *manager, void *user_data);

/**
 * TODO
 */
typedef void (*drbbdup_analyse_bb_t)(void *drcontext, instrlist_t *bb,
        drbbdup_manager_t * manager, drbbdup_case_t *case_info,
        void *user_data);

/**
 * TODO
 */
typedef void (*drbbdup_instrument_bb_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, drbbdup_manager_t * manager, drbbdup_case_t *case_info,
        void *user_data);

/**
 * TODO
 */
typedef void (*drbbdup_get_comparator_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, drbbdup_manager_t *manager, void *user_data);

/**
 * TODO
 */
DR_EXPORT void* drbbdup_get_comparator();

/**
 * TODO
 */
DR_EXPORT void drbbdup_set_comparator(void *comparator_val);

/**
 * TODO
 */
DR_EXPORT opnd_t drbbdup_get_comparator_opnd();

/** Specifies the options when initialising drbbdup. */
typedef struct {

    void *user_data;
    drbbdup_create_default_manager_t create_manager;
    drbbdup_instrument_bb_t instrument_bb;
    drbbdup_pre_analyse_bb_t pre_analyse_bb;
    drbbdup_analyse_bb_t analyse_bb;
    drbbdup_get_comparator_t get_comparator;
    size_t required_size;
} drbbdup_options_t;

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in,
        drmgr_priority_t *bb_instrum_priority);

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_exit(void);

#ifdef __cplusplus
}
#endif

#endif /* _DRBBDUP_DRBBDUP_H_ */
