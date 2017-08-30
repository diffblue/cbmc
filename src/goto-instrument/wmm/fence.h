/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

/// \file
/// Fences for instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_FENCE_H
#define CPROVER_GOTO_INSTRUMENT_WMM_FENCE_H

#include <goto-programs/goto_program.h>

class namespacet;

bool is_fence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns);

bool is_lwfence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns);

#endif // CPROVER_GOTO_INSTRUMENT_WMM_FENCE_H
