/// Module: String solver
/// Author: Diffblue Ltd.

#include "string_builtin_function.h"

#include <algorithm>
#include "string_constraint_generator.h"

/// Get the valuation of the string, given a valuation
static optionalt<std::vector<mp_integer>> eval_string(
  const array_string_exprt &a,
  const std::function<exprt(const exprt &)> &get_value);

/// Make a string from a constant array
static array_string_exprt make_string(
  const std::vector<mp_integer> &array,
  const array_typet &array_type);

string_transformation_builtin_functiont::
  string_transformation_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
  : string_builtin_functiont(return_code)
{
  PRECONDITION(fun_args.size() > 2);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input = array_pool.find(arg1.op1(), arg1.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 3, fun_args.end());
}

optionalt<exprt> string_transformation_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto &input_value = eval_string(input, get_value);
  if(!input_value.has_value())
    return {};

  std::vector<mp_integer> arg_values;
  const auto &insert = std::back_inserter(arg_values);
  const mp_integer unknown('?');
  std::transform(
    args.begin(), args.end(), insert, [&](const exprt &e) { // NOLINT
      if(const auto val = numeric_cast<mp_integer>(get_value(e)))
        return *val;
      INVARIANT(
        get_value(e).id() == ID_unknown,
        "array valuation should only contain constants and unknown");
      return unknown;
    });

  const auto result_value = eval(*input_value, arg_values);
  const auto length = from_integer(result_value.size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(result_value, type);
}

string_insertion_builtin_functiont::string_insertion_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code)
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

string_concatenation_builtin_functiont::string_concatenation_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_insertion_builtin_functiont(return_code)
{
  PRECONDITION(fun_args.size() >= 4 && fun_args.size() <= 6);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[3]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 4, fun_args.end());
}

optionalt<std::vector<mp_integer>> eval_string(
  const array_string_exprt &a,
  const std::function<exprt(const exprt &)> &get_value)
{
  if(a.id() == ID_if)
  {
    const if_exprt &ite = to_if_expr(a);
    const exprt cond = get_value(ite.cond());
    if(!cond.is_constant())
      return {};
    return cond.is_true()
             ? eval_string(to_array_string_expr(ite.true_case()), get_value)
             : eval_string(to_array_string_expr(ite.false_case()), get_value);
  }

  const exprt content = get_value(a.content());
  const auto &array = expr_try_dynamic_cast<array_exprt>(content);
  if(!array)
    return {};

  const auto &ops = array->operands();
  std::vector<mp_integer> result;
  const mp_integer unknown('?');
  const auto &insert = std::back_inserter(result);
  std::transform(
    ops.begin(), ops.end(), insert, [unknown](const exprt &e) { // NOLINT
      if(const auto i = numeric_cast<mp_integer>(e))
        return *i;
      return unknown;
    });
  return result;
}

array_string_exprt
make_string(const std::vector<mp_integer> &array, const array_typet &array_type)
{
  const typet &char_type = array_type.subtype();
  array_exprt array_expr(array_type);
  const auto &insert = std::back_inserter(array_expr.operands());
  std::transform(
    array.begin(), array.end(), insert, [&](const mp_integer &i) { // NOLINT
      return from_integer(i, char_type);
    });
  return to_array_string_expr(array_expr);
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

  std::vector<mp_integer> result(input1_value);
  result.insert(
    result.end(),
    input2_value.begin() + numeric_cast_v<std::size_t>(start_index),
    input2_value.begin() + numeric_cast_v<std::size_t>(end_index));
  return result;
}

std::vector<mp_integer> string_concat_char_builtin_functiont::eval(
  const std::vector<mp_integer> &input_value,
  const std::vector<mp_integer> &args_value) const
{
  PRECONDITION(args_value.size() == 1);
  std::vector<mp_integer> result(input_value);
  result.push_back(args_value[0]);
  return result;
}

std::vector<mp_integer> string_insertion_builtin_functiont::eval(
  const std::vector<mp_integer> &input1_value,
  const std::vector<mp_integer> &input2_value,
  const std::vector<mp_integer> &args_value) const
{
  PRECONDITION(args_value.size() >= 1 || args_value.size() <= 3);
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

  std::vector<mp_integer> result(input1_value);
  result.insert(
    result.begin() + numeric_cast_v<std::size_t>(offset),
    input2_value.begin() + numeric_cast_v<std::size_t>(start),
    input2_value.begin() + numeric_cast_v<std::size_t>(end));
  return result;
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
  const auto length = from_integer(result_value.size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(result_value, type);
}

string_builtin_function_with_no_evalt::string_builtin_function_with_no_evalt(
  const exprt &return_code,
  const function_application_exprt &f,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code), function_application(f)
{
  const std::vector<exprt> &fun_args = f.arguments();
  std::size_t i = 0;
  if(fun_args.size() >= 2 && fun_args[1].type().id() == ID_pointer)
  {
    string_res = array_pool.find(fun_args[1], fun_args[0]);
    i = 2;
  }

  for(; i < fun_args.size(); ++i)
  {
    const auto arg = expr_try_dynamic_cast<struct_exprt>(fun_args[i]);
    // TODO: use is_refined_string_type ?
    if(
      arg && arg->operands().size() == 2 &&
      arg->op1().type().id() == ID_pointer)
    {
      INVARIANT(is_refined_string_type(arg->type()), "should be a string");
      string_args.push_back(array_pool.find(arg->op1(), arg->op0()));
    }
    else
      args.push_back(fun_args[i]);
  }
}
