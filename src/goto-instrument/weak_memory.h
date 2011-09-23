/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#ifndef CPROVER_WEAK_MEMORY_H
#define CPROVER_WEAK_MEMORY_H

#include <pointer-analysis/value_sets.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

void weak_memory_tso(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions);

void weak_memory(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions);

#endif
