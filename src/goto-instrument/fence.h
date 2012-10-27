/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#ifndef FENCE_H
#define FENCE_H

#include <context.h>
#include <goto-programs/goto_program.h>

bool is_fence(
  goto_programt::instructiont instruction,
  contextt &context);

bool is_lwfence(
  goto_programt::instructiont instruction,
  contextt &context);

#endif
