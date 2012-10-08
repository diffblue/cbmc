/*******************************************************************\

Module: Remove function return values

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_RETURN_VALUES_H
#define CPROVER_REMOVE_RETURN_VALUES_H

#include <goto-programs/goto_functions.h>

class contextt;

void remove_return_values(
  contextt &context,
  goto_functionst &goto_functions);

#endif
