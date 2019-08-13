/* **********************************************************
 * Copyright (c) 2007-2010 VMware, Inc.  All rights reserved.
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
 * * Neither the name of VMware, Inc. nor the names of its contributors may be
 *   used to endorse or promote products derived from this software without
 *   specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */

#include "dr_api.h"
#include "drhit.h"

static void hit_trigger(void *drcontext, void *tag, void *user_data) {

    instrlist_t *ilist = decode_as_bb(drcontext, dr_fragment_app_pc(tag));
    instr_t *instr = instrlist_first_app(ilist);
    app_pc bb_pc = instr_get_app_pc(instr);
    instrlist_clear_and_destroy(drcontext, ilist);

    dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
    dr_get_mcontext(drcontext, &mcontext);
    mcontext.pc = bb_pc;
    dr_redirect_execution(&mcontext);
}

static void event_exit() {

    drhit_exit();
    drmgr_exit();
}

DR_EXPORT
void
dr_init(client_id_t id)
{
    drhit_options_t options = {hit_trigger, 10, NULL};
    drhit_init(&options);

    dr_register_exit_event(event_exit);



}
