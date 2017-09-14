/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Volatile Variables

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H

#include <goto-programs/goto_model.h>

bool is_volatile(
  const symbol_tablet &,
  const typet &);

void nondet_volatile(goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
