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

/// Represents an assignment that has been transformed so that the lhs
/// represents the whole object that is modified, rather than a given subpart.
/// For instance an assignment `array#2[i] = value` maybe transformed to
/// `array#2 = array#1 with [i = value]` which will be represented by
/// `lhs = array#2`, `rhs = array#1 with [i = value]`, and
/// `original_lhs_skeleton = nil[i]`. This way we can substitute `lhs` in the
/// skeleton to find the original lhs of the assignment.
template <typename lhst>
struct assignmentt final
{
  static_assert(
    std::is_base_of<exprt, lhst>::value,
    "LHS type should inherit from exprt");

  expr_skeletont original_lhs_skeleton;
  /// Left-hand-side, should be renamed to L1
  lhst lhs;
  /// Right-hand-side, should be renamed to L2
  exprt rhs;
};

/// Replace the lhs of an assignment by a new value
template <typename input_lhst, typename output_lhst>
assignmentt<output_lhst>
replace_lhs(assignmentt<input_lhst> assignment, output_lhst new_lhs)
{
  return assignmentt<output_lhst>{std::move(assignment.original_lhs_skeleton),
                                  std::move(new_lhs),
                                  std::move(assignment.rhs)};
}

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
    const assignmentt<ssa_exprt> &assignment,
    const exprt::operandst &guard);

  void
  assign_rec(const assignmentt<exprt> &assignment, exprt::operandst &guard);

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
    assignmentt<ssa_exprt> assignment,
    const exprt::operandst &guard);

  void assign_array(
    const assignmentt<index_exprt> &assignment,
    exprt::operandst &guard);

  void assign_struct_member(
    const assignmentt<member_exprt> &assignment,
    exprt::operandst &guard);

  void
  assign_if(const assignmentt<if_exprt> &assignment, exprt::operandst &guard);

  void assign_typecast(
    const assignmentt<typecast_exprt> &assignment,
    exprt::operandst &guard);

  void assign_byte_extract(
    const assignmentt<byte_extract_exprt> &assignment,
    exprt::operandst &guard);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H
