/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "array_pool.h"

#include <util/pointer_expr.h>

symbol_exprt symbol_generatort::
operator()(const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << ++symbol_count;
  irep_idt name(buf.str());
  symbol_exprt result(name, type);
#ifdef DEBUG
  created_symbols.push_back(result);
#endif
  return result;
}

exprt array_poolt::get_or_create_length(const array_string_exprt &s)
{
  if(const auto &if_expr = expr_try_dynamic_cast<if_exprt>((exprt)s))
  {
    return if_exprt{
      if_expr->cond(),
      get_or_create_length(to_array_string_expr(if_expr->true_case())),
      get_or_create_length(to_array_string_expr(if_expr->false_case()))};
  }

  auto emplace_result =
    length_of_array.emplace(s, symbol_exprt(s.length_type()));
  if(emplace_result.second)
  {
    emplace_result.first->second =
      fresh_symbol("string_length", s.length_type());
  }

  return emplace_result.first->second;
}

optionalt<exprt>
array_poolt::get_length_if_exists(const array_string_exprt &s) const
{
  auto find_result = length_of_array.find(s);
  if(find_result != length_of_array.end())
    return find_result->second;
  return {};
}

array_string_exprt
array_poolt::fresh_string(const typet &index_type, const typet &char_type)
{
  array_typet array_type{char_type, infinity_exprt(index_type)};
  symbol_exprt content = fresh_symbol("string_content", array_type);
  array_string_exprt str = to_array_string_expr(content);
  arrays_of_pointers.emplace(
    address_of_exprt(index_exprt(str, from_integer(0, index_type))), str);

  // add length to length_of_array map
  get_or_create_length(str);

  return str;
}

/// Helper function for \ref find.
/// Make a new char array for a char pointer. The size of the char array is a
/// variable with no constraint.
array_string_exprt array_poolt::make_char_array_for_char_pointer(
  const exprt &char_pointer,
  const typet &char_array_type)
{
  PRECONDITION(char_pointer.type().id() == ID_pointer);
  PRECONDITION(char_array_type.id() == ID_array);
  PRECONDITION(
    to_array_type(char_array_type).element_type().id() == ID_unsignedbv ||
    to_array_type(char_array_type).element_type().id() == ID_signedbv);

  if(char_pointer.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(char_pointer);
    const array_string_exprt t =
      make_char_array_for_char_pointer(if_expr.true_case(), char_array_type);
    const array_string_exprt f =
      make_char_array_for_char_pointer(if_expr.false_case(), char_array_type);
    const array_typet array_type(
      to_array_type(char_array_type).element_type(),
      if_exprt(
        if_expr.cond(),
        to_array_type(t.type()).size(),
        to_array_type(f.type()).size()));
    // BEWARE: this expression is possibly type-inconsistent and must not be
    // used for any purposes other than passing it to concretization.
    // Array if-exprts must be replaced (using substitute_array_access) before
    // passing the lemmas to the solver.
    return to_array_string_expr(if_exprt(if_expr.cond(), t, f, array_type));
  }

  const bool is_constant_array =
    char_pointer.id() == ID_address_of &&
    to_address_of_expr(char_pointer).object().id() == ID_index &&
    to_index_expr(to_address_of_expr(char_pointer).object()).array().id() ==
      ID_array;

  if(is_constant_array)
  {
    return to_array_string_expr(
      to_index_expr(to_address_of_expr(char_pointer).object()).array());
  }
  const std::string symbol_name = "char_array_" + id2string(char_pointer.id());
  const auto array_sym =
    to_array_string_expr(fresh_symbol(symbol_name, char_array_type));
  const auto insert_result =
    arrays_of_pointers.insert({char_pointer, array_sym});

  // add length to length_of_array map
  get_or_create_length(array_sym);

  return to_array_string_expr(insert_result.first->second);
}

/// Given an array_string_exprt, get the size of the underlying array. If that
/// size is undefined, create a new symbol for the size.
/// Then add an entry from `array_expr` to that size in the `length_of_array`
/// map.
///
/// This function should only be used at the creation of the
/// `array_string_exprt`s, as it is the only place where we can reliably refer
/// to the size in the type of the array.
static void attempt_assign_length_from_type(
  const array_string_exprt &array_expr,
  std::unordered_map<array_string_exprt, exprt, irep_hash> &length_of_array,
  symbol_generatort &symbol_generator)
{
  DATA_INVARIANT(
    array_expr.id() != ID_if,
    "attempt_assign_length_from_type does not handle if exprts");
  // This invariant seems always true, but I don't know why.
  // If we find a case where this is violated, try calling
  // attempt_assign_length_from_type on the true and false cases.
  const exprt &size_from_type = to_array_type(array_expr.type()).size();
  const exprt &size_to_assign =
    size_from_type != infinity_exprt(size_from_type.type())
      ? size_from_type
      : symbol_generator("string_length", array_expr.length_type());

  const auto emplace_result =
    length_of_array.emplace(array_expr, size_to_assign);
  INVARIANT(
    emplace_result.second,
    "attempt_assign_length_from_type should only be called when no entry"
    "for the array_string_exprt exists in the length_of_array map");
}

void array_poolt::insert(
  const exprt &pointer_expr,
  const array_string_exprt &array_expr)
{
  const auto it_bool =
    arrays_of_pointers.insert(std::make_pair(pointer_expr, array_expr));

  INVARIANT(
    it_bool.second, "should not associate two arrays to the same pointer");

  if(length_of_array.find(array_expr) == length_of_array.end())
  {
    attempt_assign_length_from_type(array_expr, length_of_array, fresh_symbol);
  }
}

/// Return a map mapping all array_string_exprt of the array_pool to their
/// length.
const std::unordered_map<array_string_exprt, exprt, irep_hash> &
array_poolt::created_strings() const
{
  return length_of_array;
}

array_string_exprt array_poolt::find(const exprt &pointer, const exprt &length)
{
  const array_typet array_type(
    to_pointer_type(pointer.type()).base_type(), length);
  const array_string_exprt array =
    make_char_array_for_char_pointer(pointer, array_type);
  return array;
}

array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg)
{
  const auto string_argument = expr_checked_cast<struct_exprt>(arg);
  return array_pool.find(string_argument.op1(), string_argument.op0());
}

array_string_exprt get_string_expr(array_poolt &array_pool, const exprt &expr)
{
  PRECONDITION(is_refined_string_type(expr.type()));
  const refined_string_exprt &str = to_string_expr(expr);
  return array_pool.find(str.content(), str.length());
}
