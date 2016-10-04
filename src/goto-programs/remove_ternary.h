/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_TERNARY_H
#define CPROVER_REMOVE_TERNARY_H

#include <goto-programs/goto_model.h>

void remove_ternary(symbol_tablet &, goto_functionst &);

void remove_ternary(goto_modelt &);

#endif
