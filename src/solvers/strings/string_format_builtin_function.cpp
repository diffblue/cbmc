/*******************************************************************\

Module: Builtin functions for String.format

Author: Romain Brenguier, Joel Allred

Date:   June 2019

\*******************************************************************/

/// \file
///  Builtin functions for String.format

#include <iterator>
#include <math.h>
#include <string>

#include "format_specifier.h"
#include "string_format_builtin_function.h"
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

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
    if(eval_is_null(arg))
      return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
    UNIMPLEMENTED;
  case format_specifiert::HEXADECIMAL_INTEGER_UPPER:
    UNIMPLEMENTED;
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
    generator.fresh_symbol,
    result,
    format_string.value(),
    inputs,
    generator.array_pool,
    // TODO: get rid of this argument
    messaget{message_handler},
    generator.ns);
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
