/*******************************************************************\

Module: Function Entering and Exiting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_FUNCTION_H
#define CPROVER_GOTO_INSTRUMENT_FUNCTION_H

#include <goto-programs/goto_functions.h>

class code_function_callt function_to_call(
  symbol_tablet &symbol_table,
  const irep_idt &id,
  const irep_idt &argument);

void function_enter(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id);

void function_exit(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id);

#endif
