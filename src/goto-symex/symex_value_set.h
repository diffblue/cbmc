/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// symex_value_sett class definition

#ifndef CPROVER_GOTO_SYMEX_SYMEX_VALUE_SET_H
#define CPROVER_GOTO_SYMEX_SYMEX_VALUE_SET_H

#include <pointer-analysis/value_set.h>
#include "renamed.h"

/// Wrapper for value_sett which ensures we access it in a consistent way.
/// In particular level 1 names should be used.
class symex_value_sett final
{
public:
  /// \copydoc value_sett::assign
  void assign(
    const renamedt<ssa_exprt, L1> &lhs,
    const renamedt<exprt, L1> &rhs,
    const namespacet &ns,
    bool is_simplified,
    bool add_to_sets)
  {
    value_set.assign(lhs.get(), rhs.get(), ns, is_simplified, add_to_sets);
  }

  /// Remove the entry corresponding to \p lhs
  void erase_symbol(const renamedt<ssa_exprt, L1> &lhs, const namespacet &ns)
  {
    value_set.erase_symbol(lhs.get(), ns);
  }

  /// Remove the entry corresponding to \p l1_identifier.
  /// Warning: which identifier is used to represent an expression is an
  /// implementation detail, it is thus preferred to use \ref erase_symbol.
  void erase_if_exists(const irep_idt &l1_identifier)
  {
    value_set.values.erase_if_exists(l1_identifier);
  }

  /// Update the entry for \p symbol_expr by erasing any values listed in
  /// \p to_erase.
  void erase(
    const symbol_exprt &symbol_expr,
    const namespacet &ns,
    const std::unordered_set<exprt, irep_hash> &to_erase)
  {
    const auto entry_index = value_set.get_index_of_symbol(
      symbol_expr.get_identifier(), symbol_expr.type(), "", ns);
    value_set.erase_values_from_entry(*entry_index, to_erase);
  }

  /// \copydoc value_sett::get_value_set(exprt, const namespacet &)
  std::vector<exprt>
  get_value_set(const renamedt<exprt, L1> &expr, const namespacet &ns) const
  {
    return value_set.get_value_set(expr.get(), ns);
  }

  /// \copydoc value_sett::make_union(const value_sett &)
  bool make_union(const symex_value_sett &new_values)
  {
    return value_set.make_union(new_values.value_set);
  }

private:
  value_sett value_set;
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_VALUE_SET_H
