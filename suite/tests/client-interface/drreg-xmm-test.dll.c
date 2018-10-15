/* **********************************************************
 * Copyright (c) 2015-2018 Google, Inc.  All rights reserved.
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

/* Tests the drreg extension */

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "client_tools.h"
#include "drreg-test-shared.h"
#include <string.h> /* memset */

#define CHECK(x, msg)                                                                \
    do {                                                                             \
        if (!(x)) {                                                                  \
            dr_fprintf(STDERR, "CHECK failed %s:%d: %s\n", __FILE__, __LINE__, msg); \
            dr_abort();                                                              \
        }                                                                            \
    } while (0);

static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *inst,
                      bool for_trace, bool translating, void *user_data)
{
    reg_id_t xmm_reg;
    drreg_status_t res;
    drvector_t xmm_allowed;
    drreg_reserve_info_t info = {
        sizeof(info),
    };

    drreg_init_and_fill_xmm_vector(&xmm_allowed, false);
    drreg_set_vector_xmm_entry(&xmm_allowed, TEST_REG_XMM1, true);

    res = drreg_reserve_register(drcontext, bb, inst, NULL, &xmm_reg);
    CHECK(res == DRREG_SUCCESS, "default reserve should always work");

    /* test restore app value back to reg */
    res = drreg_get_app_value(drcontext, bb, inst, xmm_reg, xmm_reg);
    CHECK(res == DRREG_SUCCESS || res == DRREG_ERROR_NO_APP_VALUE,
          "restore app value could only fail on dead reg");

    /* test get stolen reg to reg */
    if (dr_get_stolen_reg() != REG_NULL) {
        res = drreg_get_app_value(drcontext, bb, inst, dr_get_stolen_reg(), xmm_reg);
        CHECK(res == DRREG_ERROR_INVALID_PARAMETER,
              "get stolen reg app value should always work");
    }

    res = drreg_unreserve_register(drcontext, bb, inst, xmm_reg);
    CHECK(res == DRREG_SUCCESS, "default unreserve should always work");

    drvector_delete(&xmm_allowed);

    /* XXX i#511: add more tests */

    return DR_EMIT_DEFAULT;
}

dr_emit_flags_t
event_instru2instru(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                    bool translating)
{
    /* Test using outside of insert event */
    uint flags;
    bool dead;
    instr_t *inst = instrlist_first(bb);
    drreg_status_t res;
    drvector_t allowed;
    reg_id_t reg;

    drreg_init_and_fill_xmm_vector(&allowed, false);
    drreg_set_vector_xmm_entry(&allowed, TEST_REG_XMM1, true);

    res = drreg_reserve_register(drcontext, bb, inst, NULL, &reg);
    CHECK(res == DRREG_SUCCESS, "default reserve should always work");
    res = drreg_unreserve_register(drcontext, bb, inst, reg);
    CHECK(res == DRREG_SUCCESS, "default unreserve should always work");

    res = drreg_reserve_register(drcontext, bb, inst, &allowed, &reg);
    CHECK(res == DRREG_SUCCESS, "default reserve should always work");
    res = drreg_unreserve_register(drcontext, bb, inst, reg);
    CHECK(res == DRREG_SUCCESS, "default unreserve should always work");

    /* XXX: construct better tests with and without a dead reg available */
    res = drreg_reserve_dead_register(drcontext, bb, inst, NULL, &reg);
    if (res == DRREG_SUCCESS) {
        res = drreg_unreserve_register(drcontext, bb, inst, reg);
        CHECK(res == DRREG_SUCCESS, "default unreserve should always work");
    }

    res = drreg_reserve_xmm_register(drcontext, bb, inst, NULL, &reg);
    CHECK(res == DRREG_SUCCESS, "default reserve should always work");
    res = drreg_unreserve_xmm_register(drcontext, bb, inst, reg);
    CHECK(res == DRREG_SUCCESS, "default unreserve should always work");
    /* XXX: construct better tests with and without a dead reg available */
    res = drreg_reserve_dead_xmm_register(drcontext, bb, inst, NULL, &reg);
    if (res == DRREG_SUCCESS) {
        res = drreg_unreserve_xmm_register(drcontext, bb, inst, reg);
        CHECK(res == DRREG_SUCCESS, "default unreserve should always work");
    }

    res = drreg_reserve_aflags(drcontext, bb, inst);
    CHECK(res == DRREG_SUCCESS, "reserve of aflags should work");
    res = drreg_restore_app_aflags(drcontext, bb, inst);
    CHECK(res == DRREG_SUCCESS, "restore of app aflags should work");
    res = drreg_unreserve_aflags(drcontext, bb, inst);
    CHECK(res == DRREG_SUCCESS, "unreserve of aflags should work");

    res = drreg_aflags_liveness(drcontext, inst, &flags);
    CHECK(res == DRREG_SUCCESS, "query of aflags should work");
    res = drreg_are_aflags_dead(drcontext, inst, &dead);
    CHECK(res == DRREG_SUCCESS, "query of aflags should work");
    CHECK((dead && !TESTANY(EFLAGS_READ_ARITH, flags)) ||
              (!dead && TESTANY(EFLAGS_READ_ARITH, flags)),
          "aflags liveness inconsistency");
    res = drreg_is_register_dead(drcontext, DR_REG_START_GPR, inst, &dead);
    CHECK(res == DRREG_SUCCESS, "query of liveness should work");

    drvector_delete(&allowed);

    return DR_EMIT_DEFAULT;
}

static void
event_exit(void)
{
    if (!drmgr_unregister_bb_insertion_event(event_app_instruction) ||
        drreg_exit() != DRREG_SUCCESS)
        CHECK(false, "exit failed");

    drmgr_exit();
}

DR_EXPORT void
dr_init(client_id_t id)
{

    reg_id_t xmm_reg;
    drreg_status_t res;

    /* We actually need 3 slots (flags + 2 scratch) but we want to test using
     * a DR slot.
     */
    drreg_options_t ops = { sizeof(ops), 0 /*max slots needed*/, false };
    if (!drmgr_init() || drreg_init(&ops) != DRREG_SUCCESS)
        CHECK(false, "init failed");

    /* register events */
    dr_register_exit_event(event_exit);
    if (!drmgr_register_bb_instrumentation_event(NULL, event_app_instruction, NULL) ||
        !drmgr_register_bb_instru2instru_event(event_instru2instru, NULL))
        CHECK(false, "init failed");

    void *drcontext = dr_get_current_drcontext();
    instrlist_t *ilist = instrlist_create(drcontext);
    res = drreg_reserve_xmm_register(drcontext, ilist, NULL, NULL, &xmm_reg);
    CHECK(res == DRREG_SUCCESS, "process init test failed");
    instrlist_clear_and_destroy(drcontext, ilist);
}
