/*******************************************************************\

 Module: String solver

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <algorithm>
#include <numeric>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/expr_iterator.h>
#include <util/magic.h>
#include "string_refinement_util.h"

bool is_char_type(const typet &type)
{
  return type.id() == ID_unsignedbv &&
         to_unsignedbv_type(type).get_width() <=
           STRING_REFINEMENT_MAX_CHAR_WIDTH;
}

bool is_char_array_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_symbol)
    return is_char_array_type(ns.follow(type), ns);
  return type.id() == ID_array && is_char_type(type.subtype());
}

bool is_char_pointer_type(const typet &type)
{
  return type.id() == ID_pointer && is_char_type(type.subtype());
}

bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred)
{
  if(pred(type))
    return true;

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    const struct_union_typet &struct_type = to_struct_union_type(type);
    return std::any_of(
      struct_type.components().begin(),
      struct_type.components().end(), // NOLINTNEXTLINE
      [&](const struct_union_typet::componentt &comp) {
        return has_subtype(comp.type(), pred);
      });
  }

  return std::any_of( // NOLINTNEXTLINE
    type.subtypes().begin(), type.subtypes().end(), [&](const typet &t) {
      return has_subtype(t, pred);
    });
}

bool has_char_pointer_subtype(const typet &type)
{
  return has_subtype(type, is_char_pointer_type);
}

bool has_string_subtype(const typet &type)
{
  // NOLINTNEXTLINE
  return has_subtype(
    type, [](const typet &subtype) { return subtype == string_typet(); });
}

bool has_char_array_subexpr(const exprt &expr, const namespacet &ns)
{
  const auto it = std::find_if(
    expr.depth_begin(), expr.depth_end(), [&](const exprt &e) { // NOLINT
      return is_char_array_type(e.type(), ns);
    });
  return it != expr.depth_end();
}

sparse_arrayt::sparse_arrayt(const with_exprt &expr)
{
  auto ref = std::ref(static_cast<const exprt &>(expr));
  while(can_cast_expr<with_exprt>(ref.get()))
  {
    const auto &with_expr = expr_dynamic_cast<with_exprt>(ref.get());
    const auto current_index = numeric_cast_v<std::size_t>(with_expr.where());
    entries.emplace_back(current_index, with_expr.new_value());
    ref = with_expr.old();
  }

  // This function only handles 'with' and 'array_of' expressions
  PRECONDITION(ref.get().id() == ID_array_of);
  default_value = expr_dynamic_cast<array_of_exprt>(ref.get()).what();
}

exprt sparse_arrayt::to_if_expression(const exprt &index) const
{
  return std::accumulate(
    entries.begin(),
    entries.end(),
    default_value,
    [&](
      const exprt if_expr,
      const std::pair<std::size_t, exprt> &entry) { // NOLINT
      const exprt entry_index = from_integer(entry.first, index.type());
      const exprt &then_expr = entry.second;
      CHECK_RETURN(then_expr.type() == if_expr.type());
      const equal_exprt index_equal(index, entry_index);
      return if_exprt(index_equal, then_expr, if_expr, if_expr.type());
    });
}

interval_sparse_arrayt::interval_sparse_arrayt(const with_exprt &expr)
  : sparse_arrayt(expr)
{
  // Entries are sorted so that successive entries correspond to intervals
  std::sort(
    entries.begin(),
    entries.end(),
    [](
      const std::pair<std::size_t, exprt> &a,
      const std::pair<std::size_t, exprt> &b) { return a.first < b.first; });
}

exprt interval_sparse_arrayt::to_if_expression(const exprt &index) const
{
  return std::accumulate(
    entries.rbegin(),
    entries.rend(),
    default_value,
    [&](
      const exprt if_expr,
      const std::pair<std::size_t, exprt> &entry) { // NOLINT
      const exprt entry_index = from_integer(entry.first, index.type());
      const exprt &then_expr = entry.second;
      CHECK_RETURN(then_expr.type() == if_expr.type());
      const binary_relation_exprt index_small_eq(index, ID_le, entry_index);
      return if_exprt(index_small_eq, then_expr, if_expr, if_expr.type());
    });
}

void equation_symbol_mappingt::add(const std::size_t i, const exprt &expr)
{
  equations_containing[expr].push_back(i);
  strings_in_equation[i].push_back(expr);
}

std::vector<exprt>
equation_symbol_mappingt::find_expressions(const std::size_t i)
{
  return strings_in_equation[i];
}

std::vector<std::size_t>
equation_symbol_mappingt::find_equations(const exprt &expr)
{
  return equations_containing[expr];
}
