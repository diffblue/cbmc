/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H
#define CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H

#include <util/expr.h>
#include <util/optional.h>

class symbol_table_baset;
class symbolt;
class namespacet;
class symbol_exprt;

void add_failed_symbols(symbol_table_baset &symbol_table);

void add_failed_symbol_if_needed(
  const symbolt &symbol, symbol_table_baset &symbol_table);

irep_idt failed_symbol_id(const irep_idt &identifier);

/// Get the failed-dereference symbol for the given symbol
/// \param expr: symbol expression to get a failed symbol for
/// \param ns: global namespace
/// \return symbol expression for the failed-dereference symbol, or an empty
///   optional if none exists.
optionalt<symbol_exprt>
get_failed_symbol(const symbol_exprt &expr, const namespacet &ns);

/// Return true if, and only if, \p expr is the result of failed dereferencing.
inline bool is_failed_symbol(const exprt &expr)
{
  return expr.type().get_bool(ID_C_is_failed_symbol);
}

#endif // CPROVER_POINTER_ANALYSIS_ADD_FAILED_SYMBOLS_H
