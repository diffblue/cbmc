/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H

#include <goto-programs/goto_functions.h>

bool is_volatile(
  const contextt &context,
  const typet &type);

void nondet_volatile(
  contextt &context,
  goto_functionst &goto_functions);

#endif
