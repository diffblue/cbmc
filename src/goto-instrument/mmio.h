/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_MMIO_H
#define CPROVER_GOTO_INSTRUMENT_MMIO_H

#include <pointer-analysis/value_sets.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

void mmio(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions);

#endif
