/*******************************************************************\

Module: Fence inference

Author: Vincent Nimal

\*******************************************************************/

#ifndef CPROVER_FENCER_H
#define CPROVER_FENCER_H

#include <goto-instrument/wmm/wmm.h>
#include <goto-instrument/wmm/weak_memory.h>

#include "infer_mode.h"

class message_handlert;
class value_setst;
class goto_functionst;
class symbol_tablet;

void fence_weak_memory(
  memory_modelt model,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool SCC,
  instrumentation_strategyt event_strategy,
  unsigned unwinding_bound,
  bool no_cfg_kill,
  bool no_dependencies,
  loop_strategyt duplicate_body,
  unsigned max_var,
  unsigned max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option,
  bool hide_internals,
  bool print_graph,
  infer_modet mode,
  message_handlert& message_handler,
  bool ignore_arrays);

#endif
