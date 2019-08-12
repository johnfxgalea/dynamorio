#ifndef EXT_DRHIT_DRHIT_H_
#define EXT_DRHIT_DRHIT_H_

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
    DRMGR_PRIORITY_INSERT_DRHIT = -7000,
};

/**
 * TODO
 */
#define DRMGR_PRIORITY_NAME_DRHIT "drhit_insert"


/**
 * TODO
 */
typedef enum {
    DRHIT_SUCCESS, /**< Operation succeeded. */
    DRHIT_ERROR, /**< Operation failed. */
} drhit_status_t;

/**
 * TODO
 */
typedef void (*drhit_insert_trigger)(void *drcontext, void *tag, void *user_data);

/** Specifies the options when initialising drbbdup. */
typedef struct {
    drhit_insert_trigger insert_trigger;
    uint16_t hit_threshold;
    void *user_data;
} drhit_options_t;

/**
 * TODO
 */
DR_EXPORT drhit_status_t drhit_init(drhit_options_t *ops_in);

/**
 * TODO
 */
DR_EXPORT drhit_status_t drhit_exit(void);

/**
 * TODO
 */
DR_EXPORT void drhit_include_hit_check(void *drcontext, app_pc bb_pc, bool consider);


#ifdef __cplusplus
}
#endif

#endif /* _DRBBDUP_DRBBDUP_H_ */
