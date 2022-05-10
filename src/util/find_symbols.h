/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FIND_SYMBOLS_H
#define CPROVER_UTIL_FIND_SYMBOLS_H

#include "deprecate.h"
#include "irep.h"

#include <algorithm>
#include <set>
#include <unordered_set>

class exprt;
class symbol_exprt;
class typet;

typedef std::unordered_set<irep_idt> find_symbols_sett;

/// Returns true if one of the symbol expressions in \p src has identifier
/// \p identifier; if
/// \p include_bound_symbols is true, then bindings are included in the search.
bool has_symbol_expr(
  const exprt &src,
  const irep_idt &identifier,
  bool include_bound_symbols);

DEPRECATED(SINCE(2022, 3, 14, "use find_symbols"))
/// Add to the set \p dest the sub-expressions of \p src with id ID_symbol or
/// ID_next_symbol
void find_symbols_or_nexts(const exprt &src, find_symbols_sett &dest);

/// Add to the set \p dest the sub-expressions of \p src with id ID_symbol, for
/// both free and bound variables.
void find_symbols(const exprt &src, find_symbols_sett &dest);

/// \return set of sub-expressions of the expressions contained in the range
///   defined by \p begin and \p end which have id ID_symbol or ID_next_symbol
template <typename iteratort>
DEPRECATED(SINCE(2022, 3, 14, "use find_symbols and a local iteration"))
find_symbols_sett find_symbols_or_nexts(iteratort begin, iteratort end)
{
  static_assert(
    std::is_base_of<exprt, typename iteratort::value_type>::value,
    "find_symbols takes exprt iterators as arguments");
  find_symbols_sett result;
  std::for_each(begin, end, [&](const exprt &e) { find_symbols(e, result); });
  return result;
}

/// Find sub expressions with id ID_symbol, considering both free and bound
/// variables.
void find_symbols(
  const exprt &src,
  std::set<symbol_exprt> &dest);

/// Find sub expressions with id ID_symbol, considering both free and bound
/// variables.
inline std::set<symbol_exprt> find_symbols(const exprt &src)
{
  std::set<symbol_exprt> syms;
  find_symbols(src, syms);
  return syms;
}

/// Find identifiers of the sub expressions with id ID_symbol, considering both
/// free and bound variables.
inline find_symbols_sett find_symbol_identifiers(const exprt &src)
{
  find_symbols_sett identifiers;
  find_symbols(src, identifiers);
  return identifiers;
}

DEPRECATED(SINCE(2022, 3, 14, "use has_symbol_expr(exprt, irep_idt, bool)"))
/// \return true if one of the symbols in \p src is present in \p symbols
bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols);

/// Collect all type tags contained in \p src and add them to \p dest.
void find_type_symbols(
  const typet &src,
  find_symbols_sett &dest);

/// Collect all type tags contained in \p src and add them to \p dest.
void find_type_symbols(
  const exprt &src,
  find_symbols_sett &dest);

/// Collect type tags contained in \p src when the expression of such a type is
/// not a pointer, and add them to \p dest.
void find_non_pointer_type_symbols(
  const typet &src,
  find_symbols_sett &dest);

/// Collect type tags contained in \p src when the expression of such a type is
/// not a pointer, and add them to \p dest.
void find_non_pointer_type_symbols(
  const exprt &src,
  find_symbols_sett &dest);

/// Find identifiers of the sub expressions with id ID_symbol, considering both
/// free and bound variables, as well as any type tags.
void find_type_and_expr_symbols(
  const typet &src,
  find_symbols_sett &dest);

/// Find identifiers of the sub expressions with id ID_symbol, considering both
/// free and bound variables, as well as any type tags.
void find_type_and_expr_symbols(
  const exprt &src,
  find_symbols_sett &dest);

#endif // CPROVER_UTIL_FIND_SYMBOLS_H
