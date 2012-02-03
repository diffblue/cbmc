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

typedef enum { TSO, PSO, RMO, POWER } weak_memory_modelt;

void weak_memory(
  weak_memory_modelt model,
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions,
  bool one_partition,
  bool one_event_per_cycle,
  bool my_events,
  unsigned unwinding_bound);

#endif
