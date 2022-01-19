/*******************************************************************\

Module: Builtin functions for string concatenations

Author: Romain Brenguier, Joel Allred

\*******************************************************************/

/// \file
/// Builtin functions for string concatenations

#include "string_concatenation_builtin_function.h"

#include <algorithm>

string_concatenation_builtin_functiont::string_concatenation_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_insertion_builtin_functiont(return_code, array_pool)
{
  PRECONDITION(fun_args.size() >= 4 && fun_args.size() <= 6);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[3]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 4, fun_args.end());
}

/// Add axioms enforcing that `res` is the concatenation of `s1` with
/// the substring of `s2` starting at index `start_index'` and ending
/// at index `end_index'`.
/// Where start_index' is max(0, start_index) and end_index' is
/// max(min(end_index, s2.length), start_index')
/// If s1.length + end_index' - start_index' is greater than the maximal integer
/// of the type of res.length, then the result gets truncated to the size
/// of this maximal integer.
///
/// These axioms are:
///   1. \f$|res| = overflow ? |s_1| + end\_index' - start\_index'
///                          : max_int \f$
///   2. \f$\forall i<|s_1|. res[i]=s_1[i] \f$
///   3. \f$\forall i< |res| - |s_1|.\ res[i+|s_1|] = s_2[start\_index'+i]\f$
///
/// \param res: an array of characters expression
/// \param s1: an array of characters expression
/// \param s2: an array of characters expression
/// \param start_index: integer expression
/// \param end_index: integer expression
/// \return integer expression `0`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_concat_substr(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index)
{
  string_constraintst constraints;
  const typet &index_type = start_index.type();
  const exprt start1 = maximum(start_index, from_integer(0, index_type));
  const exprt end1 =
    maximum(minimum(end_index, array_pool.get_or_create_length(s2)), start1);

  // Axiom 1.
  constraints.existential.push_back(length_constraint_for_concat_substr(
    res, s1, s2, start_index, end_index, array_pool));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt idx = fresh_symbol("QA_index_concat", res.length_type());
    return string_constraintt(
      idx,
      zero_if_negative(array_pool.get_or_create_length(s1)),
      equal_exprt(s1[idx], res[idx]));
  }());

  // Axiom 3.
  constraints.universal.push_back([&] {
    const symbol_exprt idx2 =
      fresh_symbol("QA_index_concat2", res.length_type());
    const equal_exprt res_eq(
      res[plus_exprt(idx2, array_pool.get_or_create_length(s1))],
      s2[plus_exprt(start1, idx2)]);
    const minus_exprt upper_bound(
      array_pool.get_or_create_length(res),
      array_pool.get_or_create_length(s1));
    return string_constraintt(idx2, zero_if_negative(upper_bound), res_eq);
  }());

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with the substring of `s2` starting at index `start'`
/// and ending at index `end'`.
/// Where start_index' is max(0, start) and end' is
/// max(min(end, s2.length), start')
exprt length_constraint_for_concat_substr(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start,
  const exprt &end,
  array_poolt &array_pool)
{
  PRECONDITION(res.length_type().id() == ID_signedbv);
  const exprt start1 = maximum(start, from_integer(0, start.type()));
  const exprt end1 =
    maximum(minimum(end, array_pool.get_or_create_length(s2)), start1);
  const plus_exprt res_length(
    array_pool.get_or_create_length(s1), minus_exprt(end1, start1));
  const exprt overflow = sum_overflows(res_length);
  const exprt max_int = to_signedbv_type(res.length_type()).largest_expr();
  return equal_exprt(
    array_pool.get_or_create_length(res),
    if_exprt(overflow, max_int, res_length));
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with `s2`
exprt length_constraint_for_concat(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  array_poolt &array_pool)
{
  return equal_exprt(
    array_pool.get_or_create_length(res),
    plus_exprt(
      array_pool.get_or_create_length(s1),
      array_pool.get_or_create_length(s2)));
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with
exprt length_constraint_for_concat_char(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  array_poolt &array_pool)
{
  return equal_exprt(
    array_pool.get_or_create_length(res),
    plus_exprt(
      array_pool.get_or_create_length(s1), from_integer(1, s1.length_type())));
}

/// Add axioms enforcing that `res` is equal to the concatenation of `s1` and
/// `s2`.
///
/// \deprecated should use concat_substr instead
/// \param res: string_expression corresponding to the result
/// \param s1: the string expression to append to
/// \param s2: the string expression to append to the first one
/// \return an integer expression
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_concat(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2)
{
  exprt index_zero = from_integer(0, s2.length_type());
  return add_axioms_for_concat_substr(
    res, s1, s2, index_zero, array_pool.get_or_create_length(s2));
}

/// Add axioms corresponding to the StringBuilder.appendCodePoint(I) function
/// \deprecated java specific
/// \param f: function application with two arguments: a string and a code point
/// \return an expression
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_concat_code_point(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const typet &char_type = to_type_with_subtype(s1.content().type()).subtype();
  const typet &index_type = s1.length_type();
  const array_string_exprt code_point =
    array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_code_point(code_point, f.arguments()[3]),
    add_axioms_for_concat(res, s1, code_point));
}

std::vector<mp_integer> string_concatenation_builtin_functiont::eval(
  const std::vector<mp_integer> &input1_value,
  const std::vector<mp_integer> &input2_value,
  const std::vector<mp_integer> &args_value) const
{
  const auto start_index =
    args_value.size() > 0 && args_value[0] > 0 ? args_value[0] : mp_integer(0);
  const mp_integer input2_size(input2_value.size());
  const auto end_index =
    args_value.size() > 1
      ? std::max(std::min(args_value[1], input2_size), start_index)
      : input2_size;

  std::vector<mp_integer> eval_result(input1_value);
  eval_result.insert(
    eval_result.end(),
    input2_value.begin() + numeric_cast_v<std::size_t>(start_index),
    input2_value.begin() + numeric_cast_v<std::size_t>(end_index));
  return eval_result;
}

string_constraintst string_concatenation_builtin_functiont::constraints(
  string_constraint_generatort &generator) const

{
  auto pair = [&]() -> std::pair<exprt, string_constraintst> {
    if(args.size() == 0)
      return generator.add_axioms_for_concat(result, input1, input2);
    if(args.size() == 2)
    {
      return generator.add_axioms_for_concat_substr(
        result, input1, input2, args[0], args[1]);
    }
    UNREACHABLE;
  }();
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
}

exprt string_concatenation_builtin_functiont::length_constraint() const
{
  if(args.size() == 0)
    return length_constraint_for_concat(result, input1, input2, array_pool);
  if(args.size() == 2)
    return length_constraint_for_concat_substr(
      result, input1, input2, args[0], args[1], array_pool);
  UNREACHABLE;
}
