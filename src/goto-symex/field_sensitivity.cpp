/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#include "field_sensitivity.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "goto_symex_state.h"
#include "symex_target.h"

void field_sensitivityt::apply(const namespacet &ns, exprt &expr, bool write)
  const
{
  if(!run_apply)
    return;

  if(expr.id() != ID_address_of)
  {
    Forall_operands(it, expr)
      apply(ns, *it, write);
  }

  if(expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol) && !write)
  {
    expr = get_fields(ns, to_ssa_expr(expr));
  }
  else if(
    !write && expr.id() == ID_member &&
    to_member_expr(expr).struct_op().id() == ID_struct)
  {
    simplify(expr, ns);
  }
  else if(
    !write && expr.id() == ID_index &&
    to_index_expr(expr).array().id() == ID_array)
  {
    simplify(expr, ns);
  }
  else if(expr.id() == ID_member)
  {
    // turn a member-of-an-SSA-expression into a single SSA expression, thus
    // encoding the member as an individual symbol rather than only the full
    // struct
    member_exprt &member = to_member_expr(expr);

    if(
      member.struct_op().id() == ID_symbol &&
      member.struct_op().get_bool(ID_C_SSA_symbol) &&
      (member.struct_op().type().id() == ID_struct ||
       member.struct_op().type().id() == ID_struct_tag))
    {
      // place the entire member expression, not just the struct operand, in an
      // SSA expression
      ssa_exprt tmp = to_ssa_expr(member.struct_op());
      member.struct_op() = tmp.get_original_expr();
      tmp.set_expression(member);

      expr.swap(tmp);
    }
  }
  else if(expr.id() == ID_index)
  {
    // turn a index-of-an-SSA-expression into a single SSA expression, thus
    // encoding the index access into an array as an individual symbol rather
    // than only the full array
    index_exprt &index = to_index_expr(expr);
    simplify(index.index(), ns);

    if(
      index.array().id() == ID_symbol &&
      index.array().get_bool(ID_C_SSA_symbol) &&
      index.array().type().id() == ID_array &&
      index.index().id() == ID_constant)
    {
      // place the entire index expression, not just the array operand, in an
      // SSA expression
      ssa_exprt tmp = to_ssa_expr(index.array());
      index.array() = tmp.get_original_expr();
      tmp.set_expression(index);

      expr.swap(tmp);
    }
  }
}

exprt field_sensitivityt::get_fields(
  const namespacet &ns,
  const ssa_exprt &ssa_expr)
{
  if(ssa_expr.type().id() == ID_struct || ssa_expr.type().id() == ID_struct_tag)
  {
    const struct_typet &type = to_struct_type(ns.follow(ssa_expr.type()));
    const struct_union_typet::componentst &components = type.components();

    struct_exprt result(ssa_expr.type());
    result.reserve_operands(components.size());

    const exprt &struct_op = ssa_expr.get_original_expr();

    for(const auto &comp : components)
    {
      const member_exprt member(struct_op, comp.get_name(), comp.type());
      ssa_exprt tmp = ssa_expr;
      tmp.set_expression(member);
      result.copy_to_operands(get_fields(ns, tmp));
    }

    return std::move(result);
  }
  else if(
    ssa_expr.type().id() == ID_array &&
    to_array_type(ssa_expr.type()).size().id() == ID_constant)
  {
    const array_typet &type = to_array_type(ssa_expr.type());
    const std::size_t array_size =
      numeric_cast_v<std::size_t>(to_constant_expr(type.size()));

    array_exprt result(type);
    result.reserve_operands(array_size);

    const exprt &array = ssa_expr.get_original_expr();

    for(std::size_t i = 0; i < array_size; ++i)
    {
      const index_exprt index(array, from_integer(i, index_type()));
      ssa_exprt tmp = ssa_expr;
      tmp.set_expression(index);
      result.copy_to_operands(get_fields(ns, tmp));
    }

    return std::move(result);
  }
  else
    return ssa_expr;
}

void field_sensitivityt::field_assignments(
  const namespacet &ns,
  goto_symex_statet &state,
  const exprt &lhs,
  symex_targett &target)
{
  exprt lhs_fs = lhs;
  apply(ns, lhs_fs, false);

  bool run_apply_bak = run_apply;
  run_apply = false;
  field_assignments_rec(ns, state, lhs_fs, lhs, target);
  run_apply = run_apply_bak;
}

/// Assign to the individual fields \p lhs_fs of a non-expanded symbol \p lhs.
/// This is required whenever prior steps have updated the full object rather
/// than individual fields, e.g., in case of assignments to an array at an
/// unknown index.
/// \param ns: a namespace to resolve type symbols/tag types
/// \param state: symbolic execution state
/// \param lhs_fs: expanded symbol
/// \param lhs: non-expanded symbol
/// \param target: symbolic execution equation store
void field_sensitivityt::field_assignments_rec(
  const namespacet &ns,
  goto_symex_statet &state,
  const exprt &lhs_fs,
  const exprt &lhs,
  symex_targett &target)
{
  if(lhs == lhs_fs)
    return;
  else if(lhs_fs.id() == ID_symbol && lhs_fs.get_bool(ID_C_SSA_symbol))
  {
    exprt ssa_rhs = state.rename(lhs, ns).get();
    simplify(ssa_rhs, ns);

    ssa_exprt ssa_lhs = to_ssa_expr(lhs_fs);
    state.assignment(ssa_lhs, ssa_rhs, ns, true, true);

    // do the assignment
    target.assignment(
      state.guard.as_expr(),
      ssa_lhs,
      ssa_lhs,
      ssa_lhs.get_original_expr(),
      ssa_rhs,
      state.source,
      symex_targett::assignment_typet::STATE);
  }
  else if(lhs.type().id() == ID_struct || lhs.type().id() == ID_struct_tag)
  {
    const struct_typet &type = to_struct_type(ns.follow(lhs.type()));
    const struct_union_typet::componentst &components = type.components();

    PRECONDITION(
      components.empty() ||
      (lhs_fs.has_operands() && lhs_fs.operands().size() == components.size()));

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(const auto &comp : components)
    {
      const member_exprt member_rhs(lhs, comp.get_name(), comp.type());
      const exprt &member_lhs = *fs_it;

      field_assignments_rec(ns, state, member_lhs, member_rhs, target);
      ++fs_it;
    }
  }
  else if(const auto &type = type_try_dynamic_cast<array_typet>(lhs.type()))
  {
    const std::size_t array_size =
      numeric_cast_v<std::size_t>(to_constant_expr(type->size()));
    PRECONDITION(
      lhs_fs.has_operands() && lhs_fs.operands().size() == array_size);

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(std::size_t i = 0; i < array_size; ++i)
    {
      const index_exprt index_rhs(lhs, from_integer(i, index_type()));
      const exprt &index_lhs = *fs_it;

      field_assignments_rec(ns, state, index_lhs, index_rhs, target);
      ++fs_it;
    }
  }
  else if(lhs_fs.has_operands())
  {
    PRECONDITION(
      lhs.has_operands() && lhs_fs.operands().size() == lhs.operands().size());

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(const exprt &op : lhs.operands())
    {
      field_assignments_rec(ns, state, *fs_it, op, target);
      ++fs_it;
    }
  }
  else
  {
    UNREACHABLE;
  }
}

bool field_sensitivityt::is_divisible(
  const namespacet &ns,
  const ssa_exprt &expr)
{
  return expr != get_fields(ns, expr);
}
