#ifndef EXT_DRBBDUP_DRBBDUP_H_
#define EXT_DRBBDUP_DRBBDUP_H_

#include "dr_api.h"
#include "drmgr.h"
#include "drvector.h"

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
    void *user_data;
} drbbdup_case_t;

/**
 * TODO
 */
typedef struct {

    drbbdup_case_t default_case;
    drbbdup_case_t cases[3];
    void *user_data;
} drbbdup_manager_t;

/**
 * TODO
 */
typedef void (*drbbdup_create_default_manager_t)(void *drcontext,
        instrlist_t *bb, drbbdup_manager_t *manager, void *user_data);

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
DR_EXPORT void* drbbdup_get_comparator(void *comparator_val);

/**
 * TODO
 */
DR_EXPORT void drbbdup_set_comparator(void *comparator_val);

/**
 * TODO
 */
DR_EXPORT opnd_t drbbdup_get_comparator_opnd();

/**
 * TODO
 */
typedef void (*drbbdup_destroy_manager_data_t)(void *user_data);

/** Specifies the options when initialising drbbdup. */
typedef struct {

    void *user_data;
    drbbdup_create_default_manager_t create_manager;
    drbbdup_instrument_bb_t instrument_bb;
    drbbdup_analyse_bb_t analyse_bb;
    drbbdup_destroy_manager_data_t destroy_manager_user_data;
    drbbdup_destroy_manager_data_t destroy_case_user_data;
    drbbdup_get_comparator_t get_comparator;
    size_t required_size;
} drbbdup_options_t;

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in);

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_exit(void);

#ifdef __cplusplus
}
#endif

#endif /* _DRBBDUP_DRBBDUP_H_ */
