/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Renaming levels

#ifndef CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
#define CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H

#include <map>
#include <unordered_set>

#include <util/expr_iterator.h>
#include <util/irep.h>
#include <util/range.h>
#include <util/sharing_map.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

#include "renamed.h"

/// Wrapper for a \c current_names map, which maps each identifier to an SSA
/// expression and a counter.
/// This is extended by the different symex_level structures which are used
/// during symex to ensure static single assignment (SSA) form.
using symex_renaming_levelt =
  sharing_mapt<irep_idt, std::pair<ssa_exprt, unsigned>>;

/// Add the \c ssa_exprt of current_names to vars
DEPRECATED(SINCE(2019, 6, 5, "Unused"))
void get_variables(
  const symex_renaming_levelt &current_names,
  std::unordered_set<ssa_exprt, irep_hash> &vars);

/// Functor to set the level 0 renaming of SSA expressions.
/// Level 0 corresponds to threads.
/// The renaming is built for one particular interleaving.
struct symex_level0t
{
  /// Rename \p ssa_expr using \p thread_nr as L0 tag, unless \p ssa_expr is
  /// a guard, a shared variable or a function. \p ns is queried to decide
  /// whether we are in one of these cases.
  renamedt<ssa_exprt, L0> operator()(
    ssa_exprt ssa_expr,
    const namespacet &ns,
    unsigned thread_nr) const;
};

/// Functor to set the level 1 renaming of SSA expressions.
/// Level 1 corresponds to function frames.
/// This is to preserve locality in case of recursion
struct symex_level1t
{
  symex_renaming_levelt current_names;

  /// Assume \p ssa is not already known
  void insert(ssa_exprt ssa, unsigned index);

  /// Set the index for \p ssa to index.
  /// \return if an index for \p ssa was already know, returns it's previous
  ///   value.
  optionalt<std::pair<ssa_exprt, unsigned>>
  insert_or_replace(ssa_exprt ssa, unsigned index);

  /// \return an SSA expression similar to \p l0_expr where the L1 tag has been
  ///   set to the value in \ref current_names of the l1 object identifier of
  ///   \p l0_expr
  renamedt<ssa_exprt, L1> operator()(renamedt<ssa_exprt, L0> l0_expr) const;

  /// Insert the content of \p other into this renaming
  void restore_from(const symex_renaming_levelt &other);
};

/// Functor to set the level 2 renaming of SSA expressions.
/// Level 2 corresponds to SSA.
/// This is to ensure each variable is only assigned once.
struct symex_level2t
{
  symex_renaming_levelt current_names;

  /// Set L2 tag to correspond to the current count of the identifier of
  /// \p l1_expr's
  renamedt<ssa_exprt, L2> operator()(renamedt<ssa_exprt, L1> l1_expr) const;

  /// Counter corresponding to an identifier
  unsigned current_count(const irep_idt &identifier) const;
};

/// Undo all levels of renaming
exprt get_original_name(exprt expr);

/// Undo all levels of renaming
typet get_original_name(typet type);

#endif // CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
