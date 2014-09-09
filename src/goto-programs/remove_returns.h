/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_RETURN_VALUES_H
#define CPROVER_REMOVE_RETURN_VALUES_H

#include <goto-programs/goto_model.h>

// Turns 'return x' into an assignment to fkt#return_value,
// unless the function returns void,
// and a 'goto the_end_of_the_function'.

void remove_returns(symbol_tablet &, goto_functionst &);

void remove_returns(goto_modelt &);

#endif
