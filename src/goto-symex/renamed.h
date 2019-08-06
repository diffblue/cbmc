/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/
/// \file
/// Class for expressions or types renamed up to a given level

#ifndef CPROVER_GOTO_SYMEX_RENAMED_H
#define CPROVER_GOTO_SYMEX_RENAMED_H

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

  void simplify(const namespacet &ns)
  {
    (void)::simplify(value(), ns);
  }

  using mutator_functiont =
    std::function<optionalt<renamedt>(const renamedt &)>;

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

  template <levelt make_renamed_level>
  friend renamedt<exprt, make_renamed_level>
  make_renamed(constant_exprt constant);

  template <levelt selectively_mutate_level>
  friend void selectively_mutate(
    renamedt<exprt, selectively_mutate_level> &renamed,
    typename renamedt<exprt, selectively_mutate_level>::mutator_functiont
      get_mutated_expr);

  /// Only the friend classes can create renamedt objects
  explicit renamedt(underlyingt value) : underlyingt(std::move(value))
  {
  }
};

template <levelt level>
renamedt<exprt, level> make_renamed(constant_exprt constant)
{
  return renamedt<exprt, level>(std::move(constant));
}

/// This permits replacing subexpressions of the renamed value, so long as
/// each replacement is consistent with our current renaming level (for
/// example, replacing subexpressions of L2 expressions with ones which are
/// themselves L2 renamed).
/// The passed function will be called with each expression node in preorder
/// (i.e. parent expressions before children), and should return an empty
/// optional to make no change or a renamed expression to make a change.
template <levelt level>
void selectively_mutate(
  renamedt<exprt, level> &renamed,
  typename renamedt<exprt, level>::mutator_functiont get_mutated_expr)
{
  for(auto it = renamed.depth_begin(), itend = renamed.depth_end(); it != itend;
      ++it)
  {
    optionalt<renamedt<exprt, level>> replacement =
      get_mutated_expr(static_cast<const renamedt<exprt, level> &>(*it));

    if(replacement)
      it.mutate() = std::move(replacement->value());
  }
}

#endif // CPROVER_GOTO_SYMEX_RENAMED_H
