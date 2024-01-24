/*******************************************************************\

Module: ANSI-C Linking

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// ANSI-C Linking

#ifndef CPROVER_LINKING_CASTING_REPLACE_SYMBOL_H
#define CPROVER_LINKING_CASTING_REPLACE_SYMBOL_H

#include <util/replace_symbol.h>

/// A variant of \ref replace_symbolt that does not require types to match, but
/// instead inserts type casts as needed when replacing one symbol by another.
class casting_replace_symbolt : public replace_symbolt
{
public:
  bool replace(exprt &dest) const override;

private:
  bool replace_symbol_expr(symbol_exprt &dest) const override;
};

#endif // CPROVER_LINKING_CASTING_REPLACE_SYMBOL_H
