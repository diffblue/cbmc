/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Weak Memory Instrumentation for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
#define CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H

#include "wmm.h"

#include <util/irep.h>

class symbol_tablet;
class value_setst;
class goto_modelt;
class message_handlert;
class goto_programt;
class messaget;

void weak_memory(
  memory_modelt model,
  value_setst &,
  goto_modelt &,
  bool SCC,
  instrumentation_strategyt event_stategy,
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
  message_handlert &,
  bool ignore_arrays);

void introduce_temporaries(
  value_setst &,
  symbol_tablet &,
  const irep_idt &function,
  goto_programt &,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  messaget &message);

#endif // CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
