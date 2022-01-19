/*******************************************************************\

Module: Built-in function for String.format

Author: Romain Brenguier, Joel Allred

\*******************************************************************/

/// \file
///  Built-in function for String.format

#include <iterator>
#include <string>

#include "format_specifier.h"
#include "string_format_builtin_function.h"
#include "string_refinement_util.h"

#include <util/bitvector_expr.h>
#include <util/message.h>
#include <util/range.h>
#include <util/simplify_expr.h>

static exprt format_arg_from_string(
  const array_string_exprt &string,
  const irep_idt &id,
  array_poolt &array_pool);

string_format_builtin_functiont::string_format_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code, array_pool)
{
  PRECONDITION(fun_args.size() >= 3);
  result = array_pool.find(fun_args[1], fun_args[0]);
  const array_string_exprt format_string_expr =
    get_string_expr(array_pool, fun_args[2]);

  // List of arguments after the format string
  inputs = make_range(fun_args.begin() + 3, fun_args.end())
             .map([&](const exprt &arg) {
               INVARIANT(
                 is_refined_string_type(arg.type()),
                 "arguments of format should be strings");
               return get_string_expr(array_pool, arg);
             })
             .collect<std::vector<array_string_exprt>>();

  // format_string is only initialized if the expression is constant
  if(
    array_pool.get_or_create_length(format_string_expr).id() == ID_constant &&
    format_string_expr.content().id() == ID_array)
  {
    const auto length = numeric_cast_v<std::size_t>(
      to_constant_expr(array_pool.get_or_create_length(format_string_expr)));
    format_string = utf16_constant_array_to_java(
      to_array_expr(format_string_expr.content()), length);
  }
}

#if 0
// This code is deactivated as it is not used for now, but ultimalety this
// should be used to throw an exception when the format string is not correct
/// Used to check first argument of `String.format` is correct.
/// \param s: a string
/// \return True if the argument is a correct format string. Any '%' found
///   between format specifier means the string is invalid.
static bool check_format_string(std::string s)
{
  std::string format_specifier=
      "%(\\d+\\$)?([-#+ 0,(\\<]*)?(\\d+)?(\\.\\d+)?([tT])?([a-zA-Z%])";
  std::regex regex(format_specifier);
  std::smatch match;

  while(std::regex_search(s, match, regex))
  {
    if(match.position()!= 0)
      for(const auto &c : match.str())
        if(c=='%')
          return false;
    s=match.suffix();
  }

  for(const auto &c : s)
    if(c=='%')
      return false;

  return true;
}
#endif

/// Expression which is true when the string is equal to the literal "null"
static exprt is_null(const array_string_exprt &string, array_poolt &array_pool)
{
  return and_exprt{
    equal_exprt{array_pool.get_or_create_length(string),
                from_integer(4, string.length_type())},
    and_exprt{equal_exprt{string[0], from_integer('n', string[0].type())},
              equal_exprt{string[1], from_integer('u', string[0].type())},
              equal_exprt{string[2], from_integer('l', string[0].type())},
              equal_exprt{string[3], from_integer('l', string[0].type())}}};
}

/// Parse `s` and add axioms ensuring the output corresponds to the output of
/// String.format. Assumes the argument is a string representing one of:
/// string expr, int, float, char, boolean, hashcode, date_time.
/// The correct type will be retrieved by calling get_arg with an id depending
/// on the format specifier.
/// \param generator: constraint generator
/// \param fs: a format specifier
/// \param string_arg: format string from argument
/// \param index_type: type for indexes in strings
/// \param char_type: type of characters
/// \param message: message handler for warnings
/// \return String expression representing the output of String.format.
static std::pair<array_string_exprt, string_constraintst>
add_axioms_for_format_specifier(
  string_constraint_generatort &generator,
  const format_specifiert &fs,
  const array_string_exprt &string_arg,
  const typet &index_type,
  const typet &char_type,
  const messaget &message)
{
  string_constraintst constraints;
  array_poolt &array_pool = generator.array_pool;
  const array_string_exprt res = array_pool.fresh_string(index_type, char_type);
  std::pair<exprt, string_constraintst> return_code;
  switch(fs.conversion)
  {
  case format_specifiert::DECIMAL_INTEGER:
    return_code = generator.add_axioms_for_string_of_int(
      res, format_arg_from_string(string_arg, ID_int, array_pool), 0);
    return {res, std::move(return_code.second)};
  case format_specifiert::HEXADECIMAL_INTEGER:
    return_code = generator.add_axioms_for_string_of_int_with_radix(
      res,
      format_arg_from_string(string_arg, ID_int, array_pool),
      from_integer(16, index_type),
      16);
    return {res, std::move(return_code.second)};
  case format_specifiert::SCIENTIFIC:
    return_code = generator.add_axioms_from_float_scientific_notation(
      res, format_arg_from_string(string_arg, ID_float, array_pool));
    return {res, std::move(return_code.second)};
  case format_specifiert::DECIMAL_FLOAT:
    return_code = generator.add_axioms_for_string_of_float(
      res, format_arg_from_string(string_arg, ID_float, array_pool));
    return {res, std::move(return_code.second)};
  case format_specifiert::CHARACTER:
  {
    exprt arg_string = format_arg_from_string(string_arg, ID_char, array_pool);
    array_string_exprt &string_expr = to_array_string_expr(arg_string);
    // In the case the arg is null, the result will be equal to "null" and
    // and otherwise we just take the 4th character of the string.
    const exprt is_null_literal = is_null(string_expr, array_pool);
    constraints.existential.push_back(
      equal_exprt{array_pool.get_or_create_length(res),
                  if_exprt{is_null_literal,
                           from_integer(4, index_type),
                           from_integer(1, index_type)}});
    constraints.existential.push_back(implies_exprt{
      is_null_literal,
      and_exprt{equal_exprt{res[0], from_integer('n', char_type)},
                equal_exprt{res[1], from_integer('u', char_type)},
                equal_exprt{res[2], from_integer('l', char_type)},
                equal_exprt{res[3], from_integer('l', char_type)}}});
    constraints.existential.push_back(implies_exprt{
      not_exprt{is_null_literal},
      equal_exprt{res[0], typecast_exprt{string_expr[3], char_type}}});
    return {res, constraints};
  }
  case format_specifiert::BOOLEAN:
    return_code = generator.add_axioms_from_bool(
      res, format_arg_from_string(string_arg, ID_boolean, array_pool));
    return {res, std::move(return_code.second)};
  case format_specifiert::STRING:
  {
    const exprt arg_string = string_arg;
    const array_string_exprt string_expr = to_array_string_expr(arg_string);
    return {std::move(string_expr), {}};
  }
  case format_specifiert::HASHCODE:
    return_code = generator.add_axioms_for_string_of_int(
      res, format_arg_from_string(string_arg, "hashcode", array_pool), 0);
    return {res, std::move(return_code.second)};
  case format_specifiert::LINE_SEPARATOR:
    // TODO: the constant should depend on the system: System.lineSeparator()
    return_code = generator.add_axioms_for_constant(res, "\n");
    return {res, std::move(return_code.second)};
  case format_specifiert::PERCENT_SIGN:
    return_code = generator.add_axioms_for_constant(res, "%");
    return {res, std::move(return_code.second)};
  case format_specifiert::SCIENTIFIC_UPPER:
  case format_specifiert::GENERAL_UPPER:
  case format_specifiert::HEXADECIMAL_FLOAT_UPPER:
  case format_specifiert::CHARACTER_UPPER:
  case format_specifiert::DATE_TIME_UPPER:
  case format_specifiert::BOOLEAN_UPPER:
  case format_specifiert::STRING_UPPER:
  case format_specifiert::HASHCODE_UPPER:
  {
    format_specifiert fs_lower = fs;
    fs_lower.conversion = tolower(fs.conversion);
    auto format_specifier_result = add_axioms_for_format_specifier(
      generator, fs_lower, string_arg, index_type, char_type, message);

    const exprt return_code_upper_case =
      generator.fresh_symbol("return_code_upper_case", get_return_code_type());
    const string_to_upper_case_builtin_functiont upper_case_function(
      return_code_upper_case, res, format_specifier_result.first, array_pool);
    auto upper_case_constraints =
      upper_case_function.constraints(generator.fresh_symbol);
    merge(upper_case_constraints, std::move(format_specifier_result.second));
    return {res, std::move(upper_case_constraints)};
  }
  case format_specifiert::OCTAL_INTEGER:
    /// \todo Conversion of octal is not implemented.
  case format_specifiert::GENERAL:
    /// \todo Conversion for format specifier general is not implemented.
  case format_specifiert::HEXADECIMAL_FLOAT:
    /// \todo Conversion of hexadecimal float is not implemented.
  case format_specifiert::DATE_TIME:
    /// \todo Conversion of date-time is not implemented
    // For all these unimplemented cases we return a non-deterministic string
    message.warning() << "unimplemented format specifier: " << fs.conversion
                      << message.eom;
    return {array_pool.fresh_string(index_type, char_type), {}};
  }

  INVARIANT(false, "format specifier must belong to [bBhHsScCdoxXeEfgGaAtT%n]");
}

/// Deserialize an argument for format from \p string.
/// \p id should be one of: string_expr, int, char, boolean, float.
/// The primitive values are expected to all be encoded using 4 characters.
/// The characters of `string` must be of type `unsignedbv_typet(16)`.
static exprt format_arg_from_string(
  const array_string_exprt &string,
  const irep_idt &id,
  array_poolt &array_pool)
{
  PRECONDITION(
    to_array_type(string.content().type()).element_type() ==
    unsignedbv_typet(16));

  if(id == "string_expr")
    return string;
  if(id == ID_int)
  {
    // Assume the string has length 4
    // (int64)string.content[0] << 48 | (int64) string.content[1] << 32 |
    // (int64)string.content[2] << 16 | (int64) string.content[3]
    const signedbv_typet type{64};
    return bitor_exprt{
      bitor_exprt{shl_exprt{typecast_exprt{string[0], type}, 48},
                  shl_exprt{typecast_exprt{string[1], type}, 32}},
      bitor_exprt{shl_exprt{typecast_exprt{string[2], type}, 16},
                  typecast_exprt{string[3], type}}};
  }

  if(id == ID_char)
  {
    // Leave the string unchanged as the "null" string is used to represent null
    return string;
  }
  if(id == ID_boolean)
  {
    // We assume the string has length exactly 4, if it is "null" return false
    // and otherwise ignore the first 3 and return (bool)string.content[3]
    return if_exprt{is_null(string, array_pool),
                    false_exprt{},
                    typecast_exprt{string[3], bool_typet()}};
  }
  if(id == ID_float)
  {
    // Deserialize an int and cast to float
    const exprt as_int = format_arg_from_string(string, ID_int, array_pool);
    return typecast_exprt{as_int, floatbv_typet{}};
  }
  UNHANDLED_CASE;
}

/// Parse `s` and add axioms ensuring the output corresponds to the output of
/// String.format.
/// \param generator: constraint generator
/// \param res: string expression for the result of the format function
/// \param s: a format string
/// \param args: a vector of arguments
/// \param message: message handler for warnings
/// \return code, 0 on success
static std::pair<exprt, string_constraintst> add_axioms_for_format(
  string_constraint_generatort &generator,
  const array_string_exprt &res,
  const std::string &s,
  const std::vector<array_string_exprt> &args,
  const messaget &message)
{
  string_constraintst constraints;
  array_poolt &array_pool = generator.array_pool;
  const std::vector<format_elementt> format_strings = parse_format_string(s);
  std::vector<array_string_exprt> intermediary_strings;
  std::size_t arg_count = 0;
  const typet &char_type = res.content().type().subtype();
  const typet &index_type = res.length_type();

  array_string_exprt string_arg;

  for(const format_elementt &fe : format_strings)
  {
    if(fe.is_format_specifier())
    {
      const format_specifiert &fs = fe.get_format_specifier();

      if(
        fs.conversion != format_specifiert::PERCENT_SIGN &&
        fs.conversion != format_specifiert::LINE_SEPARATOR)
      {
        if(fs.index == -1)
        {
          INVARIANT(
            arg_count < args.size(), "number of format must match specifiers");
          string_arg = args[arg_count++];
        }
        else
        {
          INVARIANT(fs.index > 0, "index in format should be positive");
          INVARIANT(
            static_cast<std::size_t>(fs.index) <= args.size(),
            "number of format must match specifiers");

          // first argument `args[0]` corresponds to index 1
          string_arg = args[fs.index - 1];
        }
      }

      auto result = add_axioms_for_format_specifier(
        generator, fs, string_arg, index_type, char_type, message);
      merge(constraints, std::move(result.second));
      intermediary_strings.push_back(result.first);
    }
    else
    {
      const array_string_exprt str =
        array_pool.fresh_string(index_type, char_type);
      auto result = generator.add_axioms_for_constant(
        str, fe.get_format_text().get_content());
      merge(constraints, result.second);
      intermediary_strings.push_back(str);
    }
  }

  exprt return_code = from_integer(0, get_return_code_type());

  if(intermediary_strings.empty())
  {
    constraints.existential.push_back(equal_exprt(
      array_pool.get_or_create_length(res), from_integer(0, index_type)));
    return {return_code, constraints};
  }

  array_string_exprt str = intermediary_strings[0];

  if(intermediary_strings.size() == 1)
  {
    // Copy the first string
    auto result = generator.add_axioms_for_substring(
      res,
      str,
      from_integer(0, index_type),
      generator.array_pool.get_or_create_length(str));
    merge(constraints, std::move(result.second));
    return {result.first, std::move(constraints)};
  }

  // start after the first string and stop before the last
  for(std::size_t i = 1; i < intermediary_strings.size() - 1; ++i)
  {
    const array_string_exprt &intermediary = intermediary_strings[i];
    const array_string_exprt fresh =
      array_pool.fresh_string(index_type, char_type);
    auto result = generator.add_axioms_for_concat(fresh, str, intermediary);
    return_code = maximum(return_code, result.first);
    merge(constraints, std::move(result.second));
    str = fresh;
  }

  auto result =
    generator.add_axioms_for_concat(res, str, intermediary_strings.back());
  merge(constraints, std::move(result.second));
  return {maximum(result.first, return_code), std::move(constraints)};
}

static std::vector<mp_integer> deserialize_constant_int_arg(
  const std::vector<mp_integer> serialized,
  const unsigned base)
{
  PRECONDITION(serialized.size() == 4);

  // long value, to be used for other formats?
  for(std::size_t i = 0; i < 4; i++)
  {
    DATA_INVARIANT(
      serialized[i] <= 0xFFFF,
      "Component of serialized value to"
      "format must be bounded by 0xFFFF");
  }

  const int64_t int64_value =
    (serialized[0] << 48).to_long() | (serialized[1] << 32).to_long() |
    (serialized[2] << 16).to_long() | serialized[3].to_long();
  const mp_integer mp_integer_value{int64_value};
  const std::string long_as_string = integer2string(mp_integer_value, base);

  return make_range(long_as_string).map([&](char c) { return mp_integer{c}; });
}

static bool eval_is_null(const std::vector<mp_integer> &string)
{
  return string.size() == 4 && string[0] == 'n' && string[1] == 'u' &&
         string[2] == 'l' && string[3] == 'l';
}

/// Return the string to replace the format specifier, as a vector of
/// characters.
static std::vector<mp_integer> eval_format_specifier(
  const format_specifiert &fs,
  const std::vector<mp_integer> &arg)
{
  switch(fs.conversion)
  {
  case format_specifiert::DECIMAL_INTEGER:
  {
    if(eval_is_null(arg))
      return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
    return deserialize_constant_int_arg(arg, 10);
  }
  case format_specifiert::HEXADECIMAL_INTEGER:
  {
    if(eval_is_null(arg))
      return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
    auto upper_case_hex = deserialize_constant_int_arg(arg, 16);
    // convert to lower case
    return make_range(upper_case_hex).map([](const mp_integer &c) {
      if('A' <= c && c <= 'Z')
        return c + 0x20;
      return c;
    });
  }
  case format_specifiert::HEXADECIMAL_INTEGER_UPPER:
  {
    if(eval_is_null(arg))
      return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
    return deserialize_constant_int_arg(arg, 16);
  }
  case format_specifiert::SCIENTIFIC:
    UNIMPLEMENTED;
  case format_specifiert::DECIMAL_FLOAT:
    UNIMPLEMENTED;
  case format_specifiert::CHARACTER:
  {
    if(eval_is_null(arg))
      return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
    return std::vector<mp_integer>{arg[3]};
  }
  case format_specifiert::BOOLEAN:
  {
    if(arg[3] == 1)
      return std::vector<mp_integer>{'t', 'r', 'u', 'e'};
    return std::vector<mp_integer>{'f', 'a', 'l', 's', 'e'};
  }
  case format_specifiert::STRING:
    return arg;
  case format_specifiert::HASHCODE:
    UNIMPLEMENTED;
  case format_specifiert::LINE_SEPARATOR:
    // TODO: the constant should depend on the system: System.lineSeparator()
    return std::vector<mp_integer>{'\n'};
  case format_specifiert::PERCENT_SIGN:
    return std::vector<mp_integer>{'%'};
  case format_specifiert::SCIENTIFIC_UPPER:
  case format_specifiert::GENERAL_UPPER:
  case format_specifiert::HEXADECIMAL_FLOAT_UPPER:
  case format_specifiert::CHARACTER_UPPER:
  case format_specifiert::DATE_TIME_UPPER:
  case format_specifiert::BOOLEAN_UPPER:
  case format_specifiert::STRING_UPPER:
  case format_specifiert::HASHCODE_UPPER:
  {
    format_specifiert fs_lower = fs;
    fs_lower.conversion = tolower(fs.conversion);
    auto lower_case = eval_format_specifier(fs_lower, arg);
    return make_range(lower_case).map([](const mp_integer &c) {
      // TODO: incomplete
      if('a' <= c && c <= 'z')
        return c - 0x20;
      return c;
    });
  }
  case format_specifiert::OCTAL_INTEGER:
    /// \todo Conversion of octal is not implemented.
  case format_specifiert::GENERAL:
    /// \todo Conversion for format specifier general is not implemented.
  case format_specifiert::HEXADECIMAL_FLOAT:
    /// \todo Conversion of hexadecimal float is not implemented.
  case format_specifiert::DATE_TIME:
    /// \todo Conversion of date-time is not implemented
    UNIMPLEMENTED;
  }

  INVARIANT(false, "format specifier must belong to [bBhHsScCdoxXeEfgGaAtT%n]");
}

optionalt<exprt> string_format_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  if(!format_string.has_value())
    return {};

  const std::vector<format_elementt> format_strings =
    parse_format_string(format_string.value());
  std::vector<mp_integer> result_vector;
  std::size_t arg_count = 0;

  for(const format_elementt &fe : format_strings)
  {
    if(fe.is_format_specifier())
    {
      const format_specifiert &fs = fe.get_format_specifier();
      if(
        fs.conversion != format_specifiert::PERCENT_SIGN &&
        fs.conversion != format_specifiert::LINE_SEPARATOR)
      {
        std::vector<mp_integer> evaluated_char_vector;

        if(fs.index == -1)
        {
          INVARIANT(
            arg_count < inputs.size(),
            "number of format must match specifiers");
          if(auto arg_value = eval_string(inputs[arg_count++], get_value))
            evaluated_char_vector = eval_format_specifier(fs, *arg_value);
          else
            return {};
        }
        else
        {
          INVARIANT(fs.index > 0, "index in format should be positive");
          INVARIANT(
            static_cast<std::size_t>(fs.index) <= inputs.size(),
            "number of format must match specifiers");

          // first argument `args[0]` corresponds to index 1
          if(auto arg_value = eval_string(inputs[fs.index - 1], get_value))
            evaluated_char_vector = eval_format_specifier(fs, *arg_value);
          else
            return {};
        }
        std::move(
          evaluated_char_vector.begin(),
          evaluated_char_vector.end(),
          std::back_inserter(result_vector));
      }
      else if(fs.conversion == format_specifiert::PERCENT_SIGN)
      {
        result_vector.push_back('%');
      }
      else
      {
        // TODO: the character should depend on the system:
        // System.lineSeparator()
        result_vector.push_back('\n');
      }
    }
    else
    {
      for(char c : fe.get_format_text().get_content())
        result_vector.emplace_back(c);
    }
  }
  return make_string(result_vector, to_array_type(result.type()));
}

string_constraintst string_format_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  // When `format_string` was not set, leave the result non-deterministic
  if(!format_string.has_value())
    return {};

  null_message_handlert message_handler;
  auto result_constraint_pair = add_axioms_for_format(
    generator,
    result,
    format_string.value(),
    inputs,
    // TODO: get rid of this argument
    messaget{message_handler});
  INVARIANT(
    simplify_expr(result_constraint_pair.first, generator.ns).is_zero(),
    "add_axioms_for_format should return 0, meaning that formatting was"
    "successful");
  result_constraint_pair.second.existential.push_back(
    equal_exprt{return_code, from_integer(0, get_return_code_type())});
  return result_constraint_pair.second;
}

/// Return an new expression representing the length of the representation of
/// `integer`.
/// If max_length is less than the length of `integer`, the returned
/// expression will represent max_length.
/// \param pos_integer: positive (but not necessarily constant) integer for
///                     which to compute the length of the decimal
///                     representation.
/// \param max_length: max length of the decimal representation. If `max_length`
///                    is less than the length of `integer`, the returned
///                    expression will represent `max_length`. Choosing a value
///                    greater than the actual max possible length is harmless
///                    but will result in useless constraints.
/// \param length_type: type to give to the created expression
/// \param radix: radix of the output representation.
/// \return: An `exprt` representing the length of `integer`
static exprt length_of_positive_decimal_int(
  const exprt &pos_integer,
  int max_length,
  const typet &length_type,
  const unsigned long radix)
{
  if(max_length <= 1)
    return from_integer(1, length_type);

  // If the current value doesn't fit in a smaller size representation, we have
  // found the number of digits needed to represent that value.
  const mp_integer max_value_for_smaller_size =
    pow((mp_integer)radix, max_length - 1);
  return if_exprt{
    less_than(
      pos_integer,
      from_integer(max_value_for_smaller_size, pos_integer.type())),
    length_of_positive_decimal_int(
      pos_integer, max_length - 1, length_type, radix),
    from_integer(max_length, length_type)};
}

/// Compute the length of the decimal representation of an integer.
/// \param integer: (not necessarily constant) integer for which to compute the
///                 length of the decimal representation.
/// \param length_type: type to give to the created expression
/// \param radix: radix of the output representation.
/// \return: An `exprt` representing the length of `integer`
exprt length_of_decimal_int(
  const exprt &integer,
  const typet &length_type,
  const unsigned long radix)
{
  int max_pos_int_length;
  if(length_type == signedbv_typet(32))
  {
    if(radix == 10)
      max_pos_int_length = 10;
    else if(radix == 16)
      max_pos_int_length = 8;
    else
      UNIMPLEMENTED;
  }
  else
  {
    // We only handle 32-bit signed integer type for now.
    UNIMPLEMENTED;
  }

  return if_exprt{
    greater_or_equal_to(integer, from_integer(0, integer.type())),
    length_of_positive_decimal_int(
      integer, max_pos_int_length, length_type, radix),
    plus_exprt{
      length_of_positive_decimal_int(
        unary_minus_exprt{integer}, max_pos_int_length, length_type, radix),
      from_integer(1, length_type)}};
}

/// Return an expression representing the length of the format specifier
/// Does not assume that arg is constant.
exprt length_for_format_specifier(
  const format_specifiert &fs,
  const array_string_exprt &arg,
  const typet &index_type,
  array_poolt &array_pool)
{
  switch(fs.conversion)
  {
  case format_specifiert::DECIMAL_INTEGER:
  {
    return if_exprt(
      is_null(arg, array_pool),
      from_integer(4, index_type),
      length_of_decimal_int(
        format_arg_from_string(arg, ID_int, array_pool), index_type, 10));
  }
  case format_specifiert::HEXADECIMAL_INTEGER:
  case format_specifiert::HEXADECIMAL_INTEGER_UPPER:
  {
    return length_of_decimal_int(
      format_arg_from_string(arg, ID_int, array_pool), index_type, 16);
  }
  case format_specifiert::SCIENTIFIC:
    UNIMPLEMENTED;
  case format_specifiert::DECIMAL_FLOAT:
    UNIMPLEMENTED;
  case format_specifiert::CHARACTER:
  case format_specifiert::CHARACTER_UPPER:
  {
    const exprt arg_string = format_arg_from_string(arg, ID_char, array_pool);
    const array_string_exprt &string_expr = to_array_string_expr(arg_string);
    // In the case the arg is null, the result will be equal to "null" and
    // and otherwise we just take the 4th character of the string.
    return if_exprt{is_null(string_expr, array_pool),
                    from_integer(4, index_type),
                    from_integer(1, index_type)};
  }
  case format_specifiert::BOOLEAN:
  case format_specifiert::BOOLEAN_UPPER:
  {
    return if_exprt{format_arg_from_string(arg, ID_boolean, array_pool),
                    from_integer(4, index_type),
                    from_integer(5, index_type)};
  }
  case format_specifiert::STRING:
  case format_specifiert::STRING_UPPER:
  {
    const exprt arg_string =
      format_arg_from_string(arg, "string_expr", array_pool);
    const array_string_exprt string_expr = to_array_string_expr(arg_string);
    return array_pool.get_or_create_length(string_expr);
  }
  case format_specifiert::HASHCODE:
    UNIMPLEMENTED;
  case format_specifiert::LINE_SEPARATOR:
    // TODO: the constant should depend on the system: System.lineSeparator()
    return from_integer(1, index_type);
  case format_specifiert::PERCENT_SIGN:
    return from_integer(1, index_type);
  case format_specifiert::SCIENTIFIC_UPPER:
  case format_specifiert::GENERAL_UPPER:
  case format_specifiert::HEXADECIMAL_FLOAT_UPPER:
  case format_specifiert::DATE_TIME_UPPER:
  case format_specifiert::HASHCODE_UPPER:
  {
    return length_for_format_specifier(fs, arg, index_type, array_pool);
  }
  case format_specifiert::OCTAL_INTEGER:
    /// \todo Conversion of octal is not implemented.
  case format_specifiert::GENERAL:
    /// \todo Conversion for format specifier general is not implemented.
  case format_specifiert::HEXADECIMAL_FLOAT:
    /// \todo Conversion of hexadecimal float is not implemented.
  case format_specifiert::DATE_TIME:
    /// \todo Conversion of date-time is not implemented
    // For all these unimplemented cases we return a non-deterministic string
    UNIMPLEMENTED;
  }

  INVARIANT(false, "format specifier must belong to [bBhHsScCdoxXeEfgGaAtT%n]");
}

exprt string_format_builtin_functiont::length_constraint() const
{
  if(!format_string.has_value())
    return true_exprt{};

  exprt::operandst constraints;
  const std::vector<format_elementt> format_strings =
    parse_format_string(format_string.value());
  std::vector<exprt> intermediary_string_lengths;
  std::size_t arg_count = 0;
  const typet &index_type = result.length_type();

  for(const format_elementt &fe : format_strings)
  {
    if(fe.is_format_specifier())
    {
      const format_specifiert &fs = fe.get_format_specifier();
      array_string_exprt arg;
      if(
        fs.conversion != format_specifiert::PERCENT_SIGN &&
        fs.conversion != format_specifiert::LINE_SEPARATOR)
      {
        if(fs.index == -1)
        {
          INVARIANT(
            arg_count < inputs.size(),
            "number of format must match specifiers");
          arg = inputs[arg_count++];
        }
        else
        {
          INVARIANT(fs.index > 0, "index in format should be positive");
          INVARIANT(
            static_cast<std::size_t>(fs.index) <= inputs.size(),
            "number of format must match specifiers");

          // first argument `args[0]` corresponds to index 1
          arg = inputs[fs.index - 1];
        }
      }
      intermediary_string_lengths.push_back(
        length_for_format_specifier(fs, arg, index_type, array_pool));
    }
    else
    {
      intermediary_string_lengths.push_back(from_integer(
        fe.get_format_text().get_content().size(), result.length_type()));
    }
  }

  constraints.push_back(
    equal_exprt{return_code, from_integer(0, get_return_code_type())});

  if(intermediary_string_lengths.empty())
  {
    constraints.push_back(equal_exprt(
      array_pool.get_or_create_length(result), from_integer(0, index_type)));
    return conjunction(constraints);
  }

  exprt total_length = intermediary_string_lengths[0];
  for(std::size_t i = 1; i < intermediary_string_lengths.size(); ++i)
  {
    total_length =
      plus_exprt{std::move(total_length), intermediary_string_lengths[i]};
  }
  constraints.push_back(equal_exprt{array_pool.get_or_create_length(result),
                                    std::move(total_length)});

  return conjunction(constraints);
}
