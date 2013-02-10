/*******************************************************************\

Module: Interrupt Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_INTERRUPT_H
#define CPROVER_GOTO_INSTRUMENT_INTERRUPT_H

#include <pointer-analysis/value_sets.h>

#include <goto-programs/goto_functions.h>

void interrupt(
  value_setst &value_sets,
  const class symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &interrupt_handler);

#endif
