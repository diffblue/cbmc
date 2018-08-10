/// Module: String solver
/// Author: Diffblue Ltd.

#include "string_builtin_function.h"

#include <algorithm>
#include <iterator>

#include "string_constraint_generator.h"

/// Given a function `get_value` which gives a valuation to expressions, attempt
/// to find the current value of the array `a`. If the valuation of some
/// characters are missing, then return an empty optional.
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

template <typename Iter>
static array_string_exprt
make_string(Iter begin, Iter end, const array_typet &array_type)
{
  const typet &char_type = array_type.subtype();
  array_exprt array_expr(array_type);
  const auto &insert = std::back_inserter(array_expr.operands());
  std::transform(begin, end, insert, [&](const mp_integer &i) {
    return from_integer(i, char_type);
  });
  return to_array_string_expr(array_expr);
}

static array_string_exprt
make_string(const std::vector<mp_integer> &array, const array_typet &array_type)
{
  return make_string(array.begin(), array.end(), array_type);
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

string_constraintst string_concatenation_builtin_functiont::constraints(
  string_constraint_generatort &generator) const

{
  auto pair = [&]() -> std::pair<exprt, string_constraintst> {
    if(args.size() == 0)
      return add_axioms_for_concat(
        generator.fresh_symbol, result, input1, input2);
    if(args.size() == 2)
    {
      return add_axioms_for_concat_substr(
        generator.fresh_symbol, result, input1, input2, args[0], args[1]);
    }
    UNREACHABLE;
  }();
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
}

exprt string_concatenation_builtin_functiont::length_constraint() const
{
  if(args.size() == 0)
    return length_constraint_for_concat(result, input1, input2);
  if(args.size() == 2)
    return length_constraint_for_concat_substr(
      result, input1, input2, args[0], args[1]);
  UNREACHABLE;
}

optionalt<exprt> string_concat_char_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  auto input_opt = eval_string(input, get_value);
  if(!input_opt.has_value())
    return {};
  const mp_integer char_val = [&] {
    if(const auto val = numeric_cast<mp_integer>(get_value(character)))
      return *val;
    INVARIANT(
      get_value(character).id() == ID_unknown,
      "character valuation should only contain constants and unknown");
    return mp_integer(CHARACTER_FOR_UNKNOWN);
  }();
  input_opt.value().push_back(char_val);
  const auto length =
    from_integer(input_opt.value().size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(input_opt.value(), type);
}

/// Set of constraints enforcing that `result` is the concatenation
/// of `input` with `character`. These constraints are :
///   * result.length = input.length + 1
///   * forall i < max(0, result.length). result[i] = input[i]
///   * result[input.length] = character
///   * return_code = 0
string_constraintst string_concat_char_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  string_constraintst constraints;
  constraints.existential.push_back(length_constraint());
  constraints.universal.push_back([&] {
    const symbol_exprt idx =
      generator.fresh_symbol("QA_index_concat_char", result.length().type());
    const exprt upper_bound = zero_if_negative(input.length());
    return string_constraintt(
      idx, upper_bound, equal_exprt(input[idx], result[idx]));
  }());
  constraints.existential.push_back(
    equal_exprt(result[input.length()], character));
  constraints.existential.push_back(
    equal_exprt(return_code, from_integer(0, return_code.type())));
  return constraints;
}

exprt string_concat_char_builtin_functiont::length_constraint() const
{
  return length_constraint_for_concat_char(result, input);
}

optionalt<exprt> string_set_char_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  auto input_opt = eval_string(input, get_value);
  const auto char_opt = numeric_cast<mp_integer>(get_value(character));
  const auto position_opt = numeric_cast<mp_integer>(get_value(position));
  if(!input_opt || !char_opt || !position_opt)
    return {};
  if(0 <= *position_opt && *position_opt < input_opt.value().size())
    input_opt.value()[numeric_cast_v<std::size_t>(*position_opt)] = *char_opt;
  const auto length =
    from_integer(input_opt.value().size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(input_opt.value(), type);
}

/// Set of constraints ensuring that `result` is similar to `input`
/// where the character at index `position` is set to `character`.
/// If `position` is out of bounds, `input` and `result` are identical.
/// These constraints are:
///   1. res.length = str.length
///      && return_code = (position >= res.length || position < 0) ? 1 : 0
///   2. 0 <= pos < res.length ==> res[pos]=char
///   3. forall i < min(res.length, pos). res[i] = str[i]
///   4. forall pos+1 <= i < res.length. res[i] = str[i]
string_constraintst string_set_char_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  string_constraintst constraints;
  constraints.existential.push_back(length_constraint());
  constraints.existential.push_back(
    implies_exprt(
      and_exprt(
        binary_relation_exprt(
          from_integer(0, position.type()), ID_le, position),
        binary_relation_exprt(position, ID_lt, result.length())),
      equal_exprt(result[position], character)));
  constraints.universal.push_back([&] {
    const symbol_exprt q =
      generator.fresh_symbol("QA_char_set", position.type());
    const equal_exprt a3_body(result[q], input[q]);
    return string_constraintt(
      q, minimum(zero_if_negative(result.length()), position), a3_body);
  }());
  constraints.universal.push_back([&] {
    const symbol_exprt q2 =
      generator.fresh_symbol("QA_char_set2", position.type());
    const plus_exprt lower_bound(position, from_integer(1, position.type()));
    const equal_exprt a4_body(result[q2], input[q2]);
    return string_constraintt(
      q2, lower_bound, zero_if_negative(result.length()), a4_body);
  }());
  return constraints;
}

exprt string_set_char_builtin_functiont::length_constraint() const
{
  const exprt out_of_bounds = or_exprt(
    binary_relation_exprt(position, ID_ge, input.length()),
    binary_relation_exprt(
      position, ID_lt, from_integer(0, input.length().type())));
  const exprt return_value = if_exprt(
    out_of_bounds,
    from_integer(1, return_code.type()),
    from_integer(0, return_code.type()));
  return and_exprt(
    equal_exprt(result.length(), input.length()),
    equal_exprt(return_code, return_value));
}

static bool eval_is_upper_case(const mp_integer &c)
{
  // Characters between 'A' and 'Z' are upper-case
  // Characters between 0xc0 (latin capital A with grave)
  // and 0xd6 (latin capital O with diaeresis) are upper-case
  // Characters between 0xd8 (latin capital O with stroke)
  // and 0xde (latin capital thorn) are upper-case
  return ('A' <= c && c <= 'Z') || (0xc0 <= c && c <= 0xd6) ||
         (0xd8 <= c && c <= 0xde);
}

optionalt<exprt> string_to_lower_case_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  auto input_opt = eval_string(input, get_value);
  if(!input_opt)
    return {};
  for(mp_integer &c : input_opt.value())
  {
    if(eval_is_upper_case(c))
      c += 0x20;
  }
  const auto length =
    from_integer(input_opt.value().size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(input_opt.value(), type);
}

string_constraintst string_to_lower_case_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  auto pair =
    add_axioms_for_to_lower_case(generator.fresh_symbol, result, input);
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
}

optionalt<exprt> string_to_upper_case_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  auto input_opt = eval_string(input, get_value);
  if(!input_opt)
    return {};
  for(mp_integer &c : input_opt.value())
  {
    if(eval_is_upper_case(c - 0x20))
      c -= 0x20;
  }
  const auto length =
    from_integer(input_opt.value().size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(input_opt.value(), type);
}

string_constraintst string_to_upper_case_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  auto pair =
    add_axioms_for_to_upper_case(generator.fresh_symbol, result, input);
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
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

string_constraintst string_insertion_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  if(args.size() == 1)
  {
    auto pair = add_axioms_for_insert(
      generator.fresh_symbol, result, input1, input2, args[0]);
    pair.second.existential.push_back(equal_exprt(pair.first, return_code));
    return pair.second;
  }
  if(args.size() == 3)
    UNIMPLEMENTED;
  UNREACHABLE;
}

exprt string_insertion_builtin_functiont::length_constraint() const
{
  if(args.size() == 1)
    return length_constraint_for_insert(result, input1, input2);
  if(args.size() == 3)
    UNIMPLEMENTED;
  UNREACHABLE;
}

/// Constructor from arguments of a function application.
/// The arguments in `fun_args` should be in order:
/// an integer `result.length`, a character pointer `&result[0]`,
/// an expression `arg` which is to be converted to a string.
/// Other arguments are ignored by this constructor.
string_creation_builtin_functiont::string_creation_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code)
{
  PRECONDITION(fun_args.size() >= 3);
  result = array_pool.find(fun_args[1], fun_args[0]);
  arg = fun_args[2];
}

optionalt<exprt> string_of_int_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto arg_value = numeric_cast<mp_integer>(get_value(arg));
  if(!arg_value)
    return {};
  static std::string digits = "0123456789abcdefghijklmnopqrstuvwxyz";
  const auto radix_value = numeric_cast<mp_integer>(get_value(radix));
  if(!radix_value || *radix_value > digits.length())
    return {};

  mp_integer current_value = *arg_value;
  std::vector<mp_integer> right_to_left_characters;
  if(current_value < 0)
    current_value = -current_value;
  if(current_value == 0)
    right_to_left_characters.emplace_back('0');
  while(current_value > 0)
  {
    const auto digit_value = (current_value % *radix_value).to_ulong();
    right_to_left_characters.emplace_back(digits.at(digit_value));
    current_value /= *radix_value;
  }
  if(*arg_value < 0)
    right_to_left_characters.emplace_back('-');

  const auto length = right_to_left_characters.size();
  const auto length_expr = from_integer(length, result.length().type());
  const array_typet type(result.type().subtype(), length_expr);
  return make_string(
    right_to_left_characters.rbegin(), right_to_left_characters.rend(), type);
}

string_constraintst string_of_int_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  auto pair = add_axioms_for_string_of_int_with_radix(
    generator.fresh_symbol, result, arg, radix, 0, generator.ns);
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
}

exprt string_of_int_builtin_functiont::length_constraint() const
{
  const typet &type = result.length().type();
  const auto radix_opt = numeric_cast<std::size_t>(radix);
  const auto radix_value = radix_opt.has_value() ? radix_opt.value() : 2;
  const std::size_t upper_bound =
    max_printed_string_length(arg.type(), radix_value);
  const exprt negative_arg =
    binary_relation_exprt(arg, ID_le, from_integer(0, type));
  const exprt absolute_arg =
    if_exprt(negative_arg, unary_minus_exprt(arg), arg);

  exprt size_expr = from_integer(1, type);
  exprt min_int_with_current_size = from_integer(1, radix.type());
  for(std::size_t current_size = 2; current_size <= upper_bound + 1;
      ++current_size)
  {
    min_int_with_current_size = mult_exprt(radix, min_int_with_current_size);
    const exprt at_least_current_size =
      binary_relation_exprt(absolute_arg, ID_ge, min_int_with_current_size);
    size_expr = if_exprt(
      at_least_current_size, from_integer(current_size, type), size_expr);
  }

  const exprt size_expr_with_sign = if_exprt(
    negative_arg, plus_exprt(size_expr, from_integer(1, type)), size_expr);
  return equal_exprt(result.length(), size_expr_with_sign);
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

string_constraintst string_builtin_function_with_no_evalt::constraints(
  string_constraint_generatort &generator) const
{
  auto pair = generator.add_axioms_for_function_application(
    generator.fresh_symbol, function_application);
  pair.second.existential.push_back(equal_exprt(pair.first, return_code));
  return pair.second;
}
