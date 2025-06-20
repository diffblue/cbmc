/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/
/// \file
/// Class for expressions or types renamed up to a given level

#ifndef CPROVER_GOTO_SYMEX_RENAMED_H
#define CPROVER_GOTO_SYMEX_RENAMED_H

#include <util/simplify_expr_class.h>

#include <util/std_expr.h>

class ssa_exprt;

/// Symex renaming level names.
enum levelt
{
  L0 = 0,
  L1 = 1,
  L1_WITH_CONSTANT_PROPAGATION = 2,
  L2 = 3
};

/// Wrapper for expressions or types which have been renamed up to a given
/// \p level
template <typename underlyingt, levelt level>
class renamedt : private underlyingt
{
public:
  static_assert(
    std::is_base_of<exprt, underlyingt>::value ||
      std::is_base_of<typet, underlyingt>::value,
    "underlyingt should inherit from exprt or typet");

  const underlyingt &get() const
  {
    return static_cast<const underlyingt &>(*this);
  }

  void simplify(simplify_exprt &simplifier)
  {
    simplifier.simplify(value());
  }

private:
  underlyingt &value()
  {
    return static_cast<underlyingt &>(*this);
  };

  friend renamedt<ssa_exprt, L0>
  symex_level0(ssa_exprt, const namespacet &, std::size_t);
  friend struct symex_level1t;
  friend struct symex_level2t;
  friend class goto_symex_statet;

  /// Only the friend classes can create renamedt objects
  explicit renamedt(underlyingt value) : underlyingt(std::move(value))
  {
  }
};

#endif // CPROVER_GOTO_SYMEX_RENAMED_H
