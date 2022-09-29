/*******************************************************************\

Module: Free Symbols

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_FREE_SYMBOLS_H
#define CPROVER_CPROVER_FREE_SYMBOLS_H

/// \file
/// Free Symbols

#include <util/std_expr.h>

#include <functional>

void free_symbols(
  const exprt &,
  const std::function<void(const symbol_exprt &)> &);

#endif // CPROVER_CPROVER_FREE_SYMBOLS_H
