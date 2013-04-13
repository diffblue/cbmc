/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#ifndef FENCE_H
#define FENCE_H

#include <util/symbol_table.h>
#include <goto-programs/goto_program.h>

bool is_fence(
  goto_programt::instructiont instruction,
  namespacet &ns);

bool is_lwfence(
  goto_programt::instructiont instruction,
  namespacet &ns);

#endif
