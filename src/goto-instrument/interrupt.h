/*******************************************************************\

Module: Interrupt Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Interrupt Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_INTERRUPT_H
#define CPROVER_GOTO_INSTRUMENT_INTERRUPT_H

class goto_modelt;

#include "rw_set.h"

void interrupt(
  value_setst &,
  goto_modelt &,
  const irep_idt &interrupt_handler);

#endif // CPROVER_GOTO_INSTRUMENT_INTERRUPT_H
