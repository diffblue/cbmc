/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

/// \file
/// Remove function returns

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H

#include <functional>

#include <util/std_types.h>

#define RETURN_VALUE_SUFFIX "#return_value"

class goto_functionst;
class goto_model_functiont;
class goto_modelt;
class symbol_table_baset;

// Turns 'return x' into an assignment to fkt#return_value,
// unless the function returns void,
// and a 'goto the_end_of_the_function'.

void remove_returns(symbol_table_baset &, goto_functionst &);

typedef std::function<bool(const irep_idt &)> function_is_stubt;

void remove_returns(goto_model_functiont &, function_is_stubt);

void remove_returns(goto_modelt &);

// reverse the above operations
void restore_returns(symbol_table_baset &, goto_functionst &);

void restore_returns(goto_modelt &);

code_typet original_return_type(
  const symbol_table_baset &symbol_table,
  const irep_idt &function_id);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
