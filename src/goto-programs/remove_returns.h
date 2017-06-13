/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H

#include <goto-programs/goto_model.h>

#define RETURN_VALUE_SUFFIX "#return_value"

// Turns 'return x' into an assignment to fkt#return_value,
// unless the function returns void,
// and a 'goto the_end_of_the_function'.

void remove_returns(symbol_tablet &, goto_functionst &);

void remove_returns(goto_modelt &);

// reverse the above operations
void restore_returns(symbol_tablet &, goto_functionst &);

code_typet original_return_type(
  const symbol_tablet &symbol_table,
  const irep_idt &function_id);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
