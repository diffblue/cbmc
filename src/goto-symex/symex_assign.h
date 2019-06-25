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

/// Represents a assignment that has been transformed so that the lhs
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

  exprt original_lhs_skeleton;
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
    const exprt &full_lhs,
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
