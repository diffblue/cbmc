/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Volatile Variables

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H

#include <goto-programs/goto_functions.h>

void nondet_volatile(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

#endif // CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
