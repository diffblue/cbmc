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

class byte_extract_exprt;
class expr_skeletont;
class goto_symex_statet;
class ssa_exprt;
struct symex_configt;

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
