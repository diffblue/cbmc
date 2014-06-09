/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_RETURN_VALUES_H
#define CPROVER_REMOVE_RETURN_VALUES_H

#include <goto-programs/goto_model.h>

void remove_returns(symbol_tablet &, goto_functionst &);

void remove_returns(goto_modelt &);

#endif
