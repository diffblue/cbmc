/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "string_insertion_builtin_function.h"
#include <algorithm>
#include <iterator>

exprt string_insertion_builtin_functiont::length_constraint() const
{
  PRECONDITION(args.size() == 1);
  return equal_exprt(
    array_pool.get_or_create_length(result),
    plus_exprt(
      array_pool.get_or_create_length(input1),
      array_pool.get_or_create_length(input2)));
}

string_insertion_builtin_functiont::string_insertion_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code, array_pool)
{
  PRECONDITION(fun_args.size() > 4);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[4]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.push_back(fun_args[3]);
  args.insert(args.end(), fun_args.begin() + 5, fun_args.end());
}

std::vector<mp_integer> string_insertion_builtin_functiont::eval(
  const std::vector<mp_integer> &input1_value,
  const std::vector<mp_integer> &input2_value,
  const std::vector<mp_integer> &args_value) const
{
  PRECONDITION(args_value.size() >= 1 && args_value.size() <= 3);
  const auto offset = std::min(
    std::max(args_value[0], mp_integer(0)), mp_integer(input1_value.size()));
  const auto start = args_value.size() > 1
                       ? std::max(args_value[1], mp_integer(0))
                       : mp_integer(0);

  const mp_integer input2_size(input2_value.size());
  const auto end =
    args_value.size() > 2
      ? std::max(std::min(args_value[2], input2_size), mp_integer(0))
      : input2_size;

  std::vector<mp_integer> eval_result(input1_value);
  eval_result.insert(
    eval_result.begin() + numeric_cast_v<std::size_t>(offset),
    input2_value.begin() + numeric_cast_v<std::size_t>(start),
    input2_value.begin() + numeric_cast_v<std::size_t>(end));
  return eval_result;
}

optionalt<exprt> string_insertion_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto &input1_value = eval_string(input1, get_value);
  const auto &input2_value = eval_string(input2, get_value);
  if(!input2_value.has_value() || !input1_value.has_value())
    return {};

  std::vector<mp_integer> arg_values;
  const auto &insert = std::back_inserter(arg_values);
  const mp_integer unknown('?');
  std::transform(
    args.begin(), args.end(), insert, [&](const exprt &e) { // NOLINT
      if(const auto val = numeric_cast<mp_integer>(get_value(e)))
        return *val;
      return unknown;
    });

  const auto result_value = eval(*input1_value, *input2_value, arg_values);
  const auto length = from_integer(result_value.size(), result.length_type());
  const array_typet type(to_type_with_subtype(result.type()).subtype(), length);
  return make_string(result_value, type);
}

string_constraintst string_insertion_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  PRECONDITION(args.size() == 1);
  const exprt &offset = args[0];
  PRECONDITION(offset.type() == input1.length_type());
  const typet &index_type = input1.length_type();
  const exprt offset1 = maximum(
    from_integer(0, index_type),
    minimum(array_pool.get_or_create_length(input1), offset));

  string_constraintst constraints;

  // Axiom 1.
  constraints.existential.push_back(length_constraint());

  // Axiom 2.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = generator.fresh_symbol("QA_insert1", index_type);
    return string_constraintt(i, offset1, equal_exprt(result[i], input1[i]));
  }());

  // Axiom 3.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = generator.fresh_symbol("QA_insert2", index_type);
    return string_constraintt(
      i,
      zero_if_negative(array_pool.get_or_create_length(input2)),
      equal_exprt(result[plus_exprt(i, offset1)], input2[i]));
  }());

  // Axiom 4.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = generator.fresh_symbol("QA_insert3", index_type);
    return string_constraintt(
      i,
      offset1,
      zero_if_negative(array_pool.get_or_create_length(input1)),
      equal_exprt(
        result[plus_exprt(i, array_pool.get_or_create_length(input2))],
        input1[i]));
  }());

  // return_code = 0
  constraints.existential.push_back(
    equal_exprt(return_code, from_integer(0, get_return_code_type())));

  return constraints;
}
