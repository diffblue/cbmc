/*******************************************************************\

Module: String solver

Author: Diffblue Ltd.

\*******************************************************************/

#include "string_refinement_util.h"

#include <algorithm>
#include <iostream>
#include <numeric>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/magic.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/unicode.h>

bool is_char_type(const typet &type)
{
  return type.id() == ID_unsignedbv && to_unsignedbv_type(type).get_width() <=
                                         STRING_REFINEMENT_MAX_CHAR_WIDTH;
}

bool is_char_array_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
    return is_char_array_type(ns.follow_tag(to_struct_tag_type(type)), ns);
  return type.id() == ID_array &&
         is_char_type(to_array_type(type).element_type());
}

bool is_char_pointer_type(const typet &type)
{
  return type.id() == ID_pointer &&
         is_char_type(to_pointer_type(type).base_type());
}

bool has_char_pointer_subtype(const typet &type, const namespacet &ns)
{
  return has_subtype(type, is_char_pointer_type, ns);
}

bool has_char_array_subexpr(const exprt &expr, const namespacet &ns)
{
  return has_subexpr(
    expr, [&](const exprt &e) { return is_char_array_type(e.type(), ns); });
}

std::string
utf16_constant_array_to_java(const array_exprt &arr, std::size_t length)
{
  for(const auto &op : arr.operands())
    PRECONDITION(op.id() == ID_constant);

  std::wstring out(length, '?');

  for(std::size_t i = 0; i < arr.operands().size() && i < length; i++)
    out[i] = numeric_cast_v<unsigned>(to_constant_expr(arr.operands()[i]));

  return utf16_native_endian_to_java_string(out);
}

sparse_arrayt::sparse_arrayt(const with_exprt &expr)
{
  auto ref = std::ref(static_cast<const exprt &>(expr));
  while(can_cast_expr<with_exprt>(ref.get()))
  {
    const auto &with_expr = expr_dynamic_cast<with_exprt>(ref.get());
    const auto current_index =
      numeric_cast_v<std::size_t>(to_constant_expr(with_expr.where()));
    entries[current_index] = with_expr.new_value();
    ref = with_expr.old();
  }

  // This function only handles 'with' and 'array_of' expressions
  PRECONDITION(ref.get().id() == ID_array_of);
  default_value = expr_dynamic_cast<array_of_exprt>(ref.get()).what();
}

exprt sparse_arrayt::to_if_expression(
  const with_exprt &expr,
  const exprt &index)
{
  sparse_arrayt sparse_array(expr);

  return std::accumulate(
    sparse_array.entries.begin(),
    sparse_array.entries.end(),
    sparse_array.default_value,
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

interval_sparse_arrayt::interval_sparse_arrayt(
  const array_exprt &expr,
  const exprt &extra_value)
  : sparse_arrayt(extra_value)
{
  const auto &operands = expr.operands();
  exprt last_added = extra_value;
  for(std::size_t i = 0; i < operands.size(); ++i)
  {
    const std::size_t index = operands.size() - 1 - i;
    if(operands[index].id() != ID_unknown && operands[index] != last_added)
    {
      entries[index] = operands[index];
      last_added = operands[index];
    }
  }
}

interval_sparse_arrayt::interval_sparse_arrayt(
  const array_list_exprt &expr,
  const exprt &extra_value)
  : interval_sparse_arrayt(extra_value)
{
  PRECONDITION(expr.operands().size() % 2 == 0);
  for(std::size_t i = 0; i < expr.operands().size(); i += 2)
  {
    const auto index = numeric_cast<std::size_t>(expr.operands()[i]);
    INVARIANT(
      expr.operands()[i + 1].type() == extra_value.type(),
      "all values in array should have the same type");
    if(index.has_value() && expr.operands()[i + 1].id() != ID_unknown)
      entries[*index] = expr.operands()[i + 1];
  }
}

optionalt<interval_sparse_arrayt>
interval_sparse_arrayt::of_expr(const exprt &expr, const exprt &extra_value)
{
  if(const auto &array_expr = expr_try_dynamic_cast<array_exprt>(expr))
    return interval_sparse_arrayt(*array_expr, extra_value);
  if(const auto &with_expr = expr_try_dynamic_cast<with_exprt>(expr))
    return interval_sparse_arrayt(*with_expr);
  if(const auto &array_list = expr_try_dynamic_cast<array_list_exprt>(expr))
    return interval_sparse_arrayt(*array_list, extra_value);
  return {};
}

exprt interval_sparse_arrayt::at(const std::size_t index) const
{
  // First element at or after index
  const auto it = entries.lower_bound(index);
  return it != entries.end() ? it->second : default_value;
}

array_exprt interval_sparse_arrayt::concretize(
  std::size_t size,
  const typet &index_type) const
{
  const array_typet array_type(
    default_value.type(), from_integer(size, index_type));
  array_exprt array({}, array_type);
  array.operands().reserve(size);

  auto it = entries.begin();
  for(; it != entries.end() && it->first < size; ++it)
    array.operands().resize(it->first + 1, it->second);

  array.operands().resize(
    size, it == entries.end() ? default_value : it->second);
  return array;
}
