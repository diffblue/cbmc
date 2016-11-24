/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#ifndef CPROVER_WEAK_MEMORY_H
#define CPROVER_WEAK_MEMORY_H

#include "wmm.h"

class value_setst;
class goto_functionst;
class symbol_tablet;
class message_handlert;

void weak_memory(
  memory_modelt model,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool SCC,
  instrumentation_strategyt event_stategy,
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
  message_handlert& message,
  bool ignore_arrays);

void introduce_temporaries(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  const irep_idt &function,
  goto_programt &goto_program,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  messaget& message);

#endif
