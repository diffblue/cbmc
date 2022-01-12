/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#include "field_sensitivity.h"

#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "goto_symex_state.h"
#include "symex_target.h"

#define ENABLE_ARRAY_FIELD_SENSITIVITY

exprt field_sensitivityt::apply(
  const namespacet &ns,
  goto_symex_statet &state,
  ssa_exprt ssa_expr,
  bool write) const
{
  if(!run_apply || write)
    return std::move(ssa_expr);
  else
    return get_fields(ns, state, ssa_expr);
}

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

  if(!write && is_ssa_expr(expr))
  {
    return apply(ns, state, to_ssa_expr(expr), write);
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
      is_ssa_expr(member.struct_op()) &&
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
      is_ssa_expr(index.array()) && index.array().type().id() == ID_array &&
      index.index().id() == ID_constant)
    {
      // place the entire index expression, not just the array operand, in an
      // SSA expression
      ssa_exprt tmp = to_ssa_expr(index.array());
      auto l2_index = state.rename(index.index(), ns);
      l2_index.simplify(ns);
      bool was_l2 = !tmp.get_level_2().empty();
      exprt l2_size =
        state.rename(to_array_type(index.array().type()).size(), ns).get();
      if(l2_size.is_nil() && index.array().id() == ID_symbol)
      {
        // In case the array type was incomplete, attempt to retrieve it from
        // the symbol table.
        const symbolt *array_from_symbol_table = ns.get_symbol_table().lookup(
          to_symbol_expr(index.array()).get_identifier());
        if(array_from_symbol_table != nullptr)
          l2_size = to_array_type(array_from_symbol_table->type).size();
      }

      if(
        l2_size.id() == ID_constant &&
        numeric_cast_v<mp_integer>(to_constant_expr(l2_size)) <=
          max_field_sensitivity_array_size)
      {
        if(l2_index.get().id() == ID_constant)
        {
          // place the entire index expression, not just the array operand,
          // in an SSA expression
          ssa_exprt ssa_array = to_ssa_expr(index.array());
          ssa_array.remove_level_2();
          index.array() = ssa_array.get_original_expr();
          index.index() = l2_index.get();
          tmp.set_expression(index);
          if(was_l2)
            return state.rename(std::move(tmp), ns).get();
          else
            return std::move(tmp);
        }
        else if(!write)
        {
          // Expand the array and return `{array[0]; array[1]; ...}[index]`
          exprt expanded_array =
            get_fields(ns, state, to_ssa_expr(index.array()));
          return index_exprt{std::move(expanded_array), index.index()};
        }
      }
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

    struct_exprt::operandst fields;
    fields.reserve(components.size());

    const exprt &struct_op = ssa_expr.get_original_expr();

    for(const auto &comp : components)
    {
      ssa_exprt tmp = ssa_expr;
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(member_exprt{struct_op, comp.get_name(), comp.type()});
      if(was_l2)
      {
        fields.push_back(state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        fields.push_back(get_fields(ns, state, tmp));
    }

    return struct_exprt(std::move(fields), ssa_expr.type());
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(
    ssa_expr.type().id() == ID_array &&
    to_array_type(ssa_expr.type()).size().id() == ID_constant)
  {
    const mp_integer mp_array_size = numeric_cast_v<mp_integer>(
      to_constant_expr(to_array_type(ssa_expr.type()).size()));
    if(mp_array_size < 0 || mp_array_size > max_field_sensitivity_array_size)
      return ssa_expr;

    const array_typet &type = to_array_type(ssa_expr.type());
    const std::size_t array_size = numeric_cast_v<std::size_t>(mp_array_size);

    array_exprt::operandst elements;
    elements.reserve(array_size);

    const exprt &array = ssa_expr.get_original_expr();

    for(std::size_t i = 0; i < array_size; ++i)
    {
      const index_exprt index(array, from_integer(i, type.index_type()));
      ssa_exprt tmp = ssa_expr;
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(index);
      if(was_l2)
      {
        elements.push_back(state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        elements.push_back(get_fields(ns, state, tmp));
    }

    return array_exprt(std::move(elements), type);
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
  else if(is_ssa_expr(lhs_fs))
  {
    exprt ssa_rhs = state.rename(lhs, ns).get();
    simplify(ssa_rhs, ns);

    const ssa_exprt ssa_lhs = state
                                .assignment(
                                  to_ssa_expr(lhs_fs),
                                  ssa_rhs,
                                  ns,
                                  true,
                                  true,
                                  allow_pointer_unsoundness)
                                .get();

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
    PRECONDITION(lhs_fs.operands().size() == array_size);

    if(array_size > max_field_sensitivity_array_size)
      return;

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(std::size_t i = 0; i < array_size; ++i)
    {
      const index_exprt index_rhs(lhs, from_integer(i, type->index_type()));
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

bool field_sensitivityt::is_divisible(const ssa_exprt &expr) const
{
  if(expr.type().id() == ID_struct || expr.type().id() == ID_struct_tag)
    return true;

#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  if(
    expr.type().id() == ID_array &&
    to_array_type(expr.type()).size().id() == ID_constant &&
    numeric_cast_v<mp_integer>(to_constant_expr(
      to_array_type(expr.type()).size())) <= max_field_sensitivity_array_size)
  {
    return true;
  }
#endif

  return false;
}
