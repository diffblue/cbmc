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

/// Symex renaming level names.
enum levelt
{
  L0 = 0,
  L1 = 1,
  L2 = 2
};

/// Wrapper for a \c current_names map, which maps each identifier to an SSA
/// expression and a counter.
/// This is extended by the different symex_level structures which are used
/// during symex to ensure static single assignment (SSA) form.
struct symex_renaming_levelt
{
  symex_renaming_levelt() = default;
  virtual ~symex_renaming_levelt() = default;
  symex_renaming_levelt &
  operator=(const symex_renaming_levelt &other) = default;
  symex_renaming_levelt &operator=(symex_renaming_levelt &&other) = default;
  symex_renaming_levelt(const symex_renaming_levelt &other) = default;
  symex_renaming_levelt(symex_renaming_levelt &&other) = default;

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
  static void increase_counter(const current_namest::iterator &it)
  {
    ++it->second.second;
  }

  /// Add the \c ssa_exprt of current_names to vars
  void get_variables(std::unordered_set<ssa_exprt, irep_hash> &vars) const
  {
    for(const auto &pair : current_names)
      vars.insert(pair.second.first);
  }
};

/// Wrapper for expressions or types which have been renamed up to a given
/// \p level
template <typename underlyingt, levelt level>
class renamedt
{
public:
  static_assert(
    std::is_base_of<exprt, underlyingt>::value ||
      std::is_base_of<typet, underlyingt>::value,
    "underlyingt should inherit from exprt or typet");

  const underlyingt &get() const
  {
    return value;
  }

private:
  underlyingt value;

  friend struct symex_level0t;
  friend struct symex_level1t;
  friend struct symex_level2t;

  /// Only symex_levelXt classes can create renamedt objects
  explicit renamedt(underlyingt value) : value(std::move(value))
  {
  }
};

/// Functor to set the level 0 renaming of SSA expressions.
/// Level 0 corresponds to threads.
/// The renaming is built for one particular interleaving.
struct symex_level0t : public symex_renaming_levelt
{
  renamedt<ssa_exprt, L0> operator()(
    ssa_exprt ssa_expr,
    const namespacet &ns,
    unsigned thread_nr) const;

  symex_level0t() = default;
  ~symex_level0t() override = default;
};

/// Functor to set the level 1 renaming of SSA expressions.
/// Level 1 corresponds to function frames.
/// This is to preserve locality in case of recursion
struct symex_level1t : public symex_renaming_levelt
{
  renamedt<ssa_exprt, L1> operator()(renamedt<ssa_exprt, L0> l0_expr) const;

  /// Insert the content of \p other into this renaming
  void restore_from(const current_namest &other);

  symex_level1t() = default;
  ~symex_level1t() override = default;
};

/// Functor to set the level 2 renaming of SSA expressions.
/// Level 2 corresponds to SSA.
/// This is to ensure each variable is only assigned once.
struct symex_level2t : public symex_renaming_levelt
{
  renamedt<ssa_exprt, L2> operator()(renamedt<ssa_exprt, L1> l1_expr) const;

  symex_level2t() = default;
  ~symex_level2t() override = default;
  symex_level2t &operator=(const symex_level2t &other) = default;
  symex_level2t &operator=(symex_level2t &&other) = default;
  symex_level2t(const symex_level2t &other) = default;
  symex_level2t(symex_level2t &&other) = default;
};

/// Undo all levels of renaming
void get_original_name(exprt &expr);

/// Undo all levels of renaming
void get_original_name(typet &type);

#endif // CPROVER_GOTO_SYMEX_RENAMING_LEVEL_H
