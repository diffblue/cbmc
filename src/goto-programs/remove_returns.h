/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_RETURN_VALUES_H
#define CPROVER_REMOVE_RETURN_VALUES_H

#include <goto-programs/goto_functions.h>

class symbol_tablet;

void remove_returns(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

#endif
