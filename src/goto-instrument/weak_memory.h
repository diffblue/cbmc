/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#ifndef CPROVER_WEAK_MEMORY_H
#define CPROVER_WEAK_MEMORY_H

#ifndef MEMORY_MODEL
#define MEMORY_MODEL
typedef enum { TSO, PSO, RMO, POWER } weak_memory_modelt;
#endif

void weak_memory(
  weak_memory_modelt model,
  class value_setst& value_sets,
  contextt& context,
  class goto_functionst& goto_functions,
  bool SCC,
  unsigned event_stategy,
  unsigned unwinding_bound,
  bool no_cfg_kill,
  bool no_dependencies,
  unsigned max_var,
  unsigned max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option);

#endif
