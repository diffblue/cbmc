/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H
#define CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H

#include <pointer-analysis/value_sets.h>
#include <goto-programs/goto_functions.h>

void concurrency(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions);

#endif
