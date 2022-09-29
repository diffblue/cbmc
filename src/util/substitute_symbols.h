/*******************************************************************\

Module: Symbol Substitution

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SUBSTITUTE_SYMBOLS_H
#define CPROVER_UTIL_SUBSTITUTE_SYMBOLS_H

/// \file util/substitute_symbols.h
/// Symbol Substitution

#include "expr.h"

#include <map>

/// Substitute free occurrences of the variables given
/// by their identifiers in the keys of the map in the
/// given expression. Only symbol_exprt expressions are
/// substituted.
/// \returns expression after substitution,
/// or {} when no substitution took place
optionalt<exprt>
substitute_symbols(const std::map<irep_idt, exprt> &substitutions, exprt);

#endif // CPROVER_UTIL_SUBSTITUTE_SYMBOLS_H
