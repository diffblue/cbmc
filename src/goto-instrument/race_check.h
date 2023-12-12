/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
#define CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H

#ifdef LOCAL_MAY
#  include <goto-programs/goto_functions.h>
#endif

#include <util/irep.h>

class goto_modelt;
class goto_programt;
class message_handlert;
class value_setst;

void race_check(
  value_setst &,
  class symbol_table_baset &,
  const irep_idt &function_id,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program,
  message_handlert &);

void race_check(value_setst &, goto_modelt &, message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
