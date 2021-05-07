/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
#define CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H

#include <goto-programs/goto_functions.h>

class goto_modelt;
class value_setst;

void race_check(
  value_setst &,
  class symbol_tablet &,
  const irep_idt &function_id,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program);

void race_check(value_setst &, goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
