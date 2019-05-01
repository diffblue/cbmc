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

// #define ENABLE_ARRAY_FIELD_SENSITIVITY

exprt field_sensitivityt::apply(
  const namespacet &ns,
  goto_symex_statet &state,
  exprt expr,
  bool write) const
{
  if(!run_apply)
    return expr;

  if(expr.id() != ID_address_of)
  {
    Forall_operands(it, expr)
      *it = apply(ns, state, std::move(*it), write);
  }

  if(expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol) && !write)
  {
    return get_fields(ns, state, to_ssa_expr(expr));
  }
  else if(
    !write && expr.id() == ID_member &&
    to_member_expr(expr).struct_op().id() == ID_struct)
  {
    return simplify_expr(std::move(expr), ns);
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(
    !write && expr.id() == ID_index &&
    to_index_expr(expr).array().id() == ID_array)
  {
    return simplify_expr(std::move(expr), ns);
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
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
      bool was_l2 = !tmp.get_level_2().empty();

      tmp.remove_level_2();
      member.struct_op() = tmp.get_original_expr();
      tmp.set_expression(member);
      if(was_l2)
        return state.rename(std::move(tmp), ns).get();
      else
        return std::move(tmp);
    }
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
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
      bool was_l2 = !tmp.get_level_2().empty();

      tmp.remove_level_2();
      index.array() = tmp.get_original_expr();
      tmp.set_expression(index);
      if(was_l2)
        return state.rename(std::move(tmp), ns).get();
      else
        return std::move(tmp);
    }
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  return expr;
}

exprt field_sensitivityt::get_fields(
  const namespacet &ns,
  goto_symex_statet &state,
  const ssa_exprt &ssa_expr) const
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
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(member);
      if(was_l2)
      {
        result.add_to_operands(
          state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        result.add_to_operands(get_fields(ns, state, tmp));
    }

    return std::move(result);
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
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
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(index);
      if(was_l2)
      {
        result.add_to_operands(
          state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        result.add_to_operands(get_fields(ns, state, tmp));
    }

    return std::move(result);
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else
    return ssa_expr;
}

void field_sensitivityt::field_assignments(
  const namespacet &ns,
  goto_symex_statet &state,
  const ssa_exprt &lhs,
  symex_targett &target,
  bool allow_pointer_unsoundness)
{
  const exprt lhs_fs = apply(ns, state, lhs, false);

  bool run_apply_bak = run_apply;
  run_apply = false;
  field_assignments_rec(
    ns, state, lhs_fs, lhs, target, allow_pointer_unsoundness);
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
/// \param allow_pointer_unsoundness: allow pointer unsoundness
void field_sensitivityt::field_assignments_rec(
  const namespacet &ns,
  goto_symex_statet &state,
  const exprt &lhs_fs,
  const exprt &lhs,
  symex_targett &target,
  bool allow_pointer_unsoundness)
{
  if(lhs == lhs_fs)
    return;
  else if(lhs_fs.id() == ID_symbol && lhs_fs.get_bool(ID_C_SSA_symbol))
  {
    exprt ssa_rhs = state.rename(lhs, ns).get();
    simplify(ssa_rhs, ns);

    ssa_exprt ssa_lhs = to_ssa_expr(lhs_fs);
    state.assignment(
      ssa_lhs, ssa_rhs, ns, true, true, allow_pointer_unsoundness);

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

      field_assignments_rec(
        ns, state, member_lhs, member_rhs, target, allow_pointer_unsoundness);
      ++fs_it;
    }
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
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

      field_assignments_rec(
        ns, state, index_lhs, index_rhs, target, allow_pointer_unsoundness);
      ++fs_it;
    }
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(lhs_fs.has_operands())
  {
    PRECONDITION(
      lhs.has_operands() && lhs_fs.operands().size() == lhs.operands().size());

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(const exprt &op : lhs.operands())
    {
      field_assignments_rec(
        ns, state, *fs_it, op, target, allow_pointer_unsoundness);
      ++fs_it;
    }
  }
  else
  {
    UNREACHABLE;
  }
}

bool field_sensitivityt::is_divisible(const ssa_exprt &expr)
{
  if(expr.type().id() == ID_struct || expr.type().id() == ID_struct_tag)
    return true;

#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  if(
    expr.type().id() == ID_array &&
    to_array_type(expr.type()).size().id() == ID_constant)
  {
    return true;
  }
#endif

  return false;
}
