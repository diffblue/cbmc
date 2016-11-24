/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#ifndef FENCE_H
#define FENCE_H

#include <goto-programs/goto_program.h>

class namespacet;

bool is_fence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns);

bool is_lwfence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns);

#endif
