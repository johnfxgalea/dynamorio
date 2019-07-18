#ifndef EXT_DRBBDUP_DRBBDUP_H_
#define EXT_DRBBDUP_DRBBDUP_H_

#include "dr_api.h"
#include "drmgr.h"
#include "drvector.h"
#include <stdint.h>

/**
 * @file drbbdup.h
 * @brief Header for DynamoRIO Basic Block Duplication Management Extension
 */
#ifdef __cplusplus
extern "C" {
#endif

/**
 * TODO
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
    bool enable_dynamic_fp;
    bool enable_pop_threshold;
    size_t max_pop_threshold;
} drbbdup_manager_options_t;

/**
 * TODO
 */
typedef bool (*drbbdup_create_default_manager_t)(void *drbbdup_ctx,
        void *drcontext, instrlist_t *bb, drbbdup_manager_options_t *options,
        uint *default_case_value, bool *skip_post, void *user_data);

/**
 * TODO
 */
typedef void (*drbbdup_pre_analyse_bb_t)(void *drcontext, instrlist_t *bb,
        void *user_data, void **pre_analysis_result);

/**
 * TODO
 */
typedef void (*drbbdup_destroy_pre_analysis_t)(void *drcontext, void *user_data,
        void *pre_analysis_result);

/**
 * TODO
 */
typedef void (*drbbdup_analyse_bb_t)(void *drcontext, instrlist_t *bb,
        uint case_val, void *user_data, void *pre_analysis_data,
        void **analysis_result);

/**
 * TODO
 */
typedef void (*drbbdup_destroy_analysis_t)(void *drcontext, void *user_data,
        void *pre_analysis_data, void *delete_analysis_result);

/**
 * TODO
 */
typedef void (*drbbdup_nan_analyse_bb_t)(void *drcontext, instrlist_t *bb,
        void *user_data, void *pre_analysis_data, void **nan_analysis_result);

/**
 * TODO
 */
typedef void (*drbbdup_instrument_bb_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, uint case_val, void *user_data, void *pre_analysis_data,
        void *analysis_data);

/**
 * TODO
 */
typedef void (*drbbdup_nan_instrument_bb_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, void *user_data);


/**
 * TODO
 */
typedef void (*drbbdup_instrument_post_handling_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, void *user_data, void *pre_analysis_data);


/**
 * TODO
 */
typedef void (*drbbdup_get_comparator_t)(void *drcontext, instrlist_t *bb,
        instr_t *where, void *user_data, void *pre_analysis_data);

/** Specifies the options when initialising drbbdup. */
typedef struct {

    drbbdup_create_default_manager_t create_manager;
    drbbdup_pre_analyse_bb_t pre_analyse_bb;
    drbbdup_destroy_pre_analysis_t destroy_pre_analysis;
    drbbdup_analyse_bb_t analyse_bb;
    drbbdup_destroy_analysis_t destroy_analysis;
    drbbdup_instrument_bb_t instrument_bb;
    drbbdup_nan_instrument_bb_t nan_instrument_bb;
    drbbdup_get_comparator_t get_comparator;
    drbbdup_instrument_post_handling_t post_handling;
    void *user_data;
} drbbdup_options_t;

/** Specifies the options when initialising drbbdup. */
typedef struct {

    uint required_size;
    uint hit_gen_threshold;
    int dup_limit;
} drbbdup_fp_settings_t;

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

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_init(drbbdup_options_t *ops_in,
        drmgr_priority_t *bb_instrum_priority);

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_init_ex(drbbdup_options_t *ops_in,
        drbbdup_fp_settings_t *fp_settings, drmgr_priority_t *bb_instrum_priority);


/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_exit(void);

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_register_case_value(void *drbbdup_ctx,
        uint case_val, bool skip_post);

/**
 * TODO
 */
DR_EXPORT drbbdup_status_t drbbdup_unregister_case_value(void *drbbdup_ctx,
        uint case_val);

#ifdef __cplusplus
}
#endif

#endif /* _DRBBDUP_DRBBDUP_H_ */
