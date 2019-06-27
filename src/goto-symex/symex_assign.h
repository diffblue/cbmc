/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Symbolic Execution of assignments

#ifndef CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H
#define CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H

#include "symex_target.h"
#include <util/expr.h>

class goto_symex_statet;
class byte_extract_exprt;
class ssa_exprt;
struct symex_configt;

/// Expression in which some part is missing and can be substituted for another
/// expression.
///
/// For instance, a skeleton `☐[index]` where `☐` is the missing part, can be
/// applied to an expression `x` to get `x[index]` (see
/// \ref expr_skeletont::apply). It can also be composed with another skeleton,
/// let say `☐.some_field` which would give the skeleton `☐.some_field[index]`
/// (see \ref expr_skeletont::compose).
class expr_skeletont final
{
public:
  /// Empty skeleton. Applying it to an expression would give the same
  /// expression unchanged
  expr_skeletont() : skeleton(nil_exprt{})
  {
  }

  /// Replace the missing part of the current skeleton by another skeleton,
  /// ending in a bigger skeleton corresponding to the two combined.
  expr_skeletont compose(expr_skeletont other) const;

  /// Replace the missing part by the given expression, to end-up with a
  /// complete expression
  exprt apply(exprt expr) const;

  /// Create a skeleton by removing the first operand of \p e. For instance,
  /// remove_op0 on `array[index]` would give a skeleton in which `array` is
  /// missing, and applying that skeleton to `array2` would give
  /// `array2[index]`.
  static expr_skeletont remove_op0(exprt e);

private:
  /// In \c skeleton, nil_exprt is used to mark the sub expression to be
  /// substituted. The nil_exprt always appears recursively following the first
  /// operands because the only way to get a skeleton is by removing the first
  /// operand.
  exprt skeleton;

  explicit expr_skeletont(exprt e) : skeleton(std::move(e))
  {
  }
};

/// Functor for symex assignment
class symex_assignt
{
public:
  symex_assignt(
    goto_symex_statet &state,
    symex_targett::assignment_typet assignment_type,
    const namespacet &ns,
    const symex_configt &symex_config,
    symex_targett &target)
    : state(state),
      assignment_type(assignment_type),
      ns(ns),
      symex_config(symex_config),
      target(target)
  {
  }

  /// Record the assignment of value \p rhs to variable \p lhs in \p state and
  /// add the equation to target: `lhs#{n+1} == guard ? rhs#{m} : lhs#{n}`
  /// where {n} and {m} denote the current L2 indexes of lhs and rhs
  /// respectively.
  void assign_symbol(
    const ssa_exprt &lhs, // L1
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    const exprt::operandst &guard);

  void assign_rec(
    const exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);

private:
  goto_symex_statet &state;
  symex_targett::assignment_typet assignment_type;
  const namespacet &ns;
  const symex_configt &symex_config;
  symex_targett &target;

  void assign_from_struct(
    const ssa_exprt &lhs, // L1
    const expr_skeletont &full_lhs,
    const struct_exprt &rhs,
    const exprt::operandst &guard);

  void assign_non_struct_symbol(
    const ssa_exprt &lhs, // L1
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    const exprt::operandst &guard);

  /// \tparam use_update: use update_exprt instead of with_exprt when building
  ///   expressions that modify components of an array or a struct
  template <bool use_update>
  void assign_array(
    const index_exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);

  /// \tparam use_update: use update_exprt instead of with_exprt when building
  ///   expressions that modify components of an array or a struct
  template <bool use_update>
  void assign_struct_member(
    const member_exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);

  void assign_if(
    const if_exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);

  void assign_typecast(
    const typecast_exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);

  void assign_byte_extract(
    const byte_extract_exprt &lhs,
    const expr_skeletont &full_lhs,
    const exprt &rhs,
    exprt::operandst &guard);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H
