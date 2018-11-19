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

#include <util/irep.h>
#include <util/ssa_expr.h>

/// Wrapper for a \c current_names map, which maps each identifier to an SSA
/// expression and a counter.
/// This is extended by the different symex_level structures which are used
/// during symex to ensure static single assignment (SSA) form.
struct renaming_levelt
{
  virtual ~renaming_levelt() = default;

  /// Map identifier to ssa_exprt and counter
  typedef std::map<irep_idt, std::pair<ssa_exprt, unsigned>> current_namest;
  current_namest current_names;

  /// Counter corresponding to an identifier
  unsigned current_count(const irep_idt &identifier) const
  {
    const auto it = current_names.find(identifier);
    return it == current_names.end() ? 0 : it->second.second;
  }

  /// Increase the counter corresponding to an identifier
  void increase_counter(const irep_idt &identifier)
  {
    PRECONDITION(current_names.find(identifier) != current_names.end());
    ++current_names[identifier].second;
  }

  /// Add the \c ssa_exprt of current_names to vars
  void get_variables(std::unordered_set<ssa_exprt, irep_hash> &vars) const
  {
    for(const auto &pair : current_names)
      vars.insert(pair.second.first);
  }
};

/// Functor to set the level 0 renaming of SSA expressions.
/// Level 0 corresponds to threads.
/// The renaming is built for one particular interleaving.
struct symex_level0t : public renaming_levelt
{
  void
  operator()(ssa_exprt &ssa_expr, const namespacet &ns, unsigned thread_nr);

  symex_level0t() = default;
  ~symex_level0t() override = default;
};

/// Functor to set the level 1 renaming of SSA expressions.
/// Level 1 corresponds to function frames.
/// This is to preserve locality in case of recursion
struct symex_level1t : public renaming_levelt
{
  void operator()(ssa_exprt &ssa_expr);

  /// Insert the content of \p other into this renaming
  void restore_from(const current_namest &other);

  symex_level1t() = default;
  ~symex_level1t() override = default;
};

/// Functor to set the level 2 renaming of SSA expressions.
/// Level 2 corresponds to SSA.
/// This is to ensure each variable is only assigned once.
struct symex_level2t : public renaming_levelt
{
  symex_level2t() = default;
  ~symex_level2t() override = default;
};

#endif // CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
