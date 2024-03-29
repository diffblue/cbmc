/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions generating strings from other
///   types, in particular int, long, float, double, char, bool

#include "string_constraint_generator.h"

#include <util/deprecate.h>
#include <util/mathematical_expr.h>
#include <util/simplify_expr.h>

#include <cmath>

/// If the expression is a constant expression then we get the value of it as
/// an unsigned long. If not we return a default value.
/// \param expr: input expression
/// \param def: default value to return if we cannot evaluate expr
/// \param ns: namespace used to simplify the expression
/// \return the output as an unsigned long
static unsigned long to_integer_or_default(
  const exprt &expr,
  unsigned long def,
  const namespacet &ns)
{
  if(const auto i = numeric_cast<unsigned long>(simplify_expr(expr, ns)))
    return *i;
  return def;
}

/// Add axioms corresponding to the String.valueOf(J) java function.
/// \deprecated should use add_axioms_from_int instead
/// \param f: function application with one long argument
/// \return a new string expression
DEPRECATED(SINCE(2017, 10, 5, "use add_axioms_for_string_of_int instead"))
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_from_long(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3 || f.arguments().size() == 4);
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  if(f.arguments().size() == 4)
    return add_axioms_for_string_of_int_with_radix(
      res, f.arguments()[2], f.arguments()[3], 0);
  else
    return add_axioms_for_string_of_int(res, f.arguments()[2], 0);
}

/// Add axioms stating that the returned string equals "true" when the Boolean
/// expression is true and "false" when it is false.
/// \deprecated This is Java specific and should be implemented in Java instead
/// \param res: string expression for the result
/// \param b: Boolean expression
/// \return code 0 on success
DEPRECATED(SINCE(2017, 10, 5, "Java specific, should be implemented in Java"))
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_from_bool(
  const array_string_exprt &res,
  const exprt &b)
{
  const typet &char_type = to_type_with_subtype(res.content().type()).subtype();
  PRECONDITION(b.type() == bool_typet() || b.type().id() == ID_c_bool);
  string_constraintst constraints;
  typecast_exprt eq(b, bool_typet());

  // We add axioms:
  // a1 : eq => res = |"true"|
  // a2 : forall i < |"true"|. eq => res[i]="true"[i]
  // a3 : !eq => res = |"false"|
  // a4 : forall i < |"false"|. !eq => res[i]="false"[i]

  std::string str_true = "true";
  const implies_exprt a1(
    eq, equal_to(array_pool.get_or_create_length(res), str_true.length()));
  constraints.existential.push_back(a1);

  for(std::size_t i = 0; i < str_true.length(); i++)
  {
    exprt chr = from_integer(str_true[i], char_type);
    implies_exprt a2(eq, equal_exprt(res[i], chr));
    constraints.existential.push_back(a2);
  }

  std::string str_false = "false";
  const implies_exprt a3(
    not_exprt(eq),
    equal_to(array_pool.get_or_create_length(res), str_false.length()));
  constraints.existential.push_back(a3);

  for(std::size_t i = 0; i < str_false.length(); i++)
  {
    exprt chr = from_integer(str_false[i], char_type);
    implies_exprt a4(not_exprt(eq), equal_exprt(res[i], chr));
    constraints.existential.push_back(a4);
  }

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(I) or String.valueOf(J) Java functions applied
/// on the integer expression.
/// \param res: string expression for the result
/// \param input_int: a signed integer expression
/// \param max_size: a maximal size for the string representation (default 0,
///   which is interpreted to mean "as large as is needed for this type")
/// \return code 0 on success
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_string_of_int(
  const array_string_exprt &res,
  const exprt &input_int,
  size_t max_size)
{
  const constant_exprt radix = from_integer(10, input_int.type());
  return add_axioms_for_string_of_int_with_radix(
    res, input_int, radix, max_size);
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(II) or String.valueOf(JI) Java functions applied
/// on the integer expression.
/// \param res: string expression for the result
/// \param input_int: a signed integer expression
/// \param radix: the radix to use
/// \param max_size: a maximal size for the string representation (default 0,
///   which is interpreted to mean "as large as is needed for this type")
/// \return code 0 on success
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_string_of_int_with_radix(
  const array_string_exprt &res,
  const exprt &input_int,
  const exprt &radix,
  size_t max_size)
{
  PRECONDITION(max_size < std::numeric_limits<size_t>::max());
  const typet &type = input_int.type();
  PRECONDITION(type.id() == ID_signedbv);

  /// Most of the time we can evaluate radix as an integer. The value 0 is used
  /// to indicate when we can't tell what the radix is.
  const unsigned long radix_ul = to_integer_or_default(radix, 0, ns);
  CHECK_RETURN((radix_ul >= 2 && radix_ul <= 36) || radix_ul == 0);

  if(max_size == 0)
  {
    max_size = max_printed_string_length(type, radix_ul);
    CHECK_RETURN(max_size < std::numeric_limits<size_t>::max());
  }

  const typet &char_type = to_type_with_subtype(res.content().type()).subtype();
  const typecast_exprt radix_as_char(radix, char_type);
  const typecast_exprt radix_input_type(radix, type);
  const bool strict_formatting = true;

  auto result1 = get_conjuncts_for_correct_number_format(
    res, radix_as_char, radix_ul, max_size, strict_formatting);
  auto result2 = add_axioms_for_characters_in_integer_string(
    input_int,
    type,
    strict_formatting,
    res,
    max_size,
    radix_input_type,
    radix_ul);
  result2.existential.push_back(conjunction(std::move(result1)));
  return {from_integer(0, get_return_code_type()), std::move(result2)};
}

/// Returns the integer value represented by the character.
/// \param chr: a character expression in the following set:
///   0123456789abcdef
/// \return an integer expression
static exprt int_of_hex_char(const exprt &chr)
{
  const exprt zero_char = from_integer('0', chr.type());
  const exprt nine_char = from_integer('9', chr.type());
  const exprt a_char = from_integer('a', chr.type());
  return if_exprt(
    binary_relation_exprt(chr, ID_gt, nine_char),
    plus_exprt(from_integer(10, chr.type()), minus_exprt(chr, a_char)),
    minus_exprt(chr, zero_char));
}

/// Add axioms stating that the string `res` corresponds to the integer
/// argument written in hexadecimal.
/// \deprecated use add_axioms_from_int_with_radix instead
/// \param res: string expression for the result
/// \param i: an integer argument
/// \return code 0 on success
DEPRECATED(SINCE(2017, 10, 5, "use add_axioms_for_string_of_int_with_radix"))
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_from_int_hex(
  const array_string_exprt &res,
  const exprt &i)
{
  const typet &type = i.type();
  PRECONDITION(type.id() == ID_signedbv);
  string_constraintst constraints;
  const typet &index_type = res.length_type();
  const typet &char_type = to_type_with_subtype(res.content().type()).subtype();
  exprt sixteen = from_integer(16, index_type);
  exprt minus_char = from_integer('-', char_type);
  exprt zero_char = from_integer('0', char_type);
  exprt nine_char = from_integer('9', char_type);
  exprt a_char = from_integer('a', char_type);
  exprt f_char = from_integer('f', char_type);

  size_t max_size = 8;
  constraints.existential.push_back(and_exprt(
    greater_than(array_pool.get_or_create_length(res), 0),
    less_than_or_equal_to(array_pool.get_or_create_length(res), max_size)));

  for(size_t size = 1; size <= max_size; size++)
  {
    exprt sum = from_integer(0, type);
    exprt all_numbers = true_exprt();
    exprt chr = res[0];

    for(size_t j = 0; j < size; j++)
    {
      chr = res[j];
      exprt chr_int = int_of_hex_char(chr);
      sum = plus_exprt(mult_exprt(sum, sixteen), typecast_exprt(chr_int, type));
      or_exprt is_number(
        and_exprt(
          binary_relation_exprt(chr, ID_ge, zero_char),
          binary_relation_exprt(chr, ID_le, nine_char)),
        and_exprt(
          binary_relation_exprt(chr, ID_ge, a_char),
          binary_relation_exprt(chr, ID_le, f_char)));
      all_numbers = and_exprt(all_numbers, is_number);
    }

    const equal_exprt premise =
      equal_to(array_pool.get_or_create_length(res), size);
    constraints.existential.push_back(
      implies_exprt(premise, and_exprt(equal_exprt(i, sum), all_numbers)));

    // disallow 0s at the beginning
    if(size > 1)
      constraints.existential.push_back(
        implies_exprt(premise, not_exprt(equal_exprt(res[0], zero_char))));
  }
  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms corresponding to the Integer.toHexString(I) java function
/// \param f: function application with an integer argument
/// \return code 0 on success
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_from_int_hex(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  return add_axioms_from_int_hex(res, f.arguments()[2]);
}

/// Add axioms making the return value true if the given string is a correct
/// number in the given radix
/// \param str: string expression
/// \param radix_as_char: the radix as an expression of the same type as the
///   characters in str
/// \param radix_ul: the radix, which should be between 2 and 36, or 0, in
///   which case the return value will work for any radix
/// \param max_size: maximum number of characters
/// \param strict_formatting: if true, don't allow a leading plus, redundant
///   zeros or upper case letters
std::vector<exprt>
string_constraint_generatort::get_conjuncts_for_correct_number_format(
  const array_string_exprt &str,
  const exprt &radix_as_char,
  const unsigned long radix_ul,
  const std::size_t max_size,
  const bool strict_formatting)
{
  std::vector<exprt> conjuncts;
  const typet &char_type = to_type_with_subtype(str.content().type()).subtype();
  const typet &index_type = str.length_type();

  const exprt &chr = str[0];
  const equal_exprt starts_with_minus(chr, from_integer('-', char_type));
  const equal_exprt starts_with_plus(chr, from_integer('+', char_type));
  const exprt starts_with_digit =
    is_digit_with_radix(chr, strict_formatting, radix_as_char, radix_ul);

  // |str| > 0
  const exprt non_empty = greater_or_equal_to(
    array_pool.get_or_create_length(str), from_integer(1, index_type));
  conjuncts.push_back(non_empty);

  if(strict_formatting)
  {
    // str[0] = '-' || is_digit_with_radix(str[0], radix)
    const or_exprt correct_first(starts_with_minus, starts_with_digit);
    conjuncts.push_back(correct_first);
  }
  else
  {
    // str[0] = '-' || str[0] = '+' || is_digit_with_radix(str[0], radix)
    const or_exprt correct_first(
      starts_with_minus, starts_with_digit, starts_with_plus);
    conjuncts.push_back(correct_first);
  }

  // str[0]='+' or '-' ==> |str| > 1
  const implies_exprt contains_digit(
    or_exprt(starts_with_minus, starts_with_plus),
    greater_or_equal_to(
      array_pool.get_or_create_length(str), from_integer(2, index_type)));
  conjuncts.push_back(contains_digit);

  // |str| <= max_size
  conjuncts.push_back(
    less_than_or_equal_to(array_pool.get_or_create_length(str), max_size));

  // forall 1 <= i < |str| . is_digit_with_radix(str[i], radix)
  // We unfold the above because we know that it will be used for all i up to
  // |str|, and |str| <= max_size.
  for(std::size_t index = 1; index < max_size; ++index)
  {
    /// index < length => is_digit_with_radix(str[index], radix)
    const implies_exprt character_at_index_is_digit(
      greater_or_equal_to(
        array_pool.get_or_create_length(str),
        from_integer(index + 1, index_type)),
      is_digit_with_radix(
        str[index], strict_formatting, radix_as_char, radix_ul));
    conjuncts.push_back(character_at_index_is_digit);
  }

  if(strict_formatting)
  {
    const exprt zero_char = from_integer('0', char_type);

    // no_leading_zero : str[0] = '0' => |str| = 1
    const implies_exprt no_leading_zero(
      equal_exprt(chr, zero_char),
      equal_to(
        array_pool.get_or_create_length(str), from_integer(1, index_type)));
    conjuncts.push_back(no_leading_zero);

    // no_leading_zero_after_minus : str[0]='-' => str[1]!='0'
    implies_exprt no_leading_zero_after_minus(
      starts_with_minus, not_exprt(equal_exprt(str[1], zero_char)));
    conjuncts.push_back(no_leading_zero_after_minus);
  }
  return conjuncts;
}

/// Add axioms connecting the characters in the input string to the value of the
/// output integer. It is constructive because it gives a formula for input_int
/// in terms of the characters in str.
/// \param input_int: the integer represented by str
/// \param type: the type for input_int
/// \param strict_formatting: if true, don't allow a leading plus, redundant
///   zeros or upper case letters
/// \param str: input string
/// \param max_string_length: the maximum length str can have
/// \param radix: the radix, with the same type as input_int
/// \param radix_ul: the radix as an unsigned long, or 0 if that can't be
///   determined
string_constraintst
string_constraint_generatort::add_axioms_for_characters_in_integer_string(
  const exprt &input_int,
  const typet &type,
  const bool strict_formatting,
  const array_string_exprt &str,
  const std::size_t max_string_length,
  const exprt &radix,
  const unsigned long radix_ul)
{
  string_constraintst constraints;
  const typet &char_type = to_type_with_subtype(str.content().type()).subtype();

  const equal_exprt starts_with_minus(str[0], from_integer('-', char_type));
  const constant_exprt zero_expr = from_integer(0, type);

  exprt sum = get_numeric_value_from_character(
    str[0], char_type, type, strict_formatting, radix_ul);

  /// Deal with size==1 case separately. There are axioms from
  /// add_axioms_for_correct_number_format which say that the string must
  /// contain at least one digit, so we don't have to worry about "+" or "-".
  constraints.existential.push_back(implies_exprt(
    equal_to(array_pool.get_or_create_length(str), 1),
    equal_exprt(input_int, sum)));

  for(size_t size = 2; size <= max_string_length; size++)
  {
    // sum_0 := numeric value of res[0] (which is 0 if res[0] is '-')
    // For each 1<=j<max_string_length, we have:
    // sum_j := radix * sum_{j-1} + numeric value of res[j]
    // no_overflow_j := sum_{j-1} == (radix * sum_{j-1} / radix)
    //                  && sum_j >= sum_{j - 1}
    //   (the first part avoid overflows in the multiplication and the second
    //     one in the addition of the definition of sum_j)
    // For all 1<=size<=max_string_length we add axioms:
    // a5 : |res| >= size => no_overflow_j (only added when overflow possible)
    // a6 : |res| == size && res[0] is a digit for radix =>
    //        input_int == sum_{size-1}
    // a7 : |res| == size && res[0] == '-' => input_int == -sum_{size-1}

    const mult_exprt radix_sum(sum, radix);
    // new_sum = radix * sum + (numeric value of res[j])
    const exprt new_sum = plus_exprt(
      radix_sum,
      get_numeric_value_from_character(
        str[size - 1], char_type, type, strict_formatting, radix_ul));

    // An overflow can happen when reaching the last index which can contain
    // a digit, which is `max_string_length - 2` because of the space left for
    // a minus sign. That assumes that we were able to identify the radix. If we
    // weren't then we check for overflow on every index.
    std::optional<exprt> no_overflow;
    if(size - 1 >= max_string_length - 2 || radix_ul == 0)
    {
      no_overflow = and_exprt{equal_exprt(sum, div_exprt(radix_sum, radix)),
                              binary_relation_exprt(new_sum, ID_ge, radix_sum)};
    }
    sum = new_sum;

    exprt length_expr = array_pool.get_or_create_length(str);

    if(no_overflow.has_value())
    {
      const binary_predicate_exprt string_length_ge_size{
        length_expr, ID_ge, from_integer(size, length_expr.type())};
      const implies_exprt a5(string_length_ge_size, *no_overflow);
      constraints.existential.push_back(a5);
    }

    const equal_exprt string_length_equals_size = equal_to(length_expr, size);

    const implies_exprt a6(
      and_exprt(string_length_equals_size, not_exprt(starts_with_minus)),
      equal_exprt(input_int, sum));
    constraints.existential.push_back(a6);

    const implies_exprt a7(
      and_exprt(string_length_equals_size, starts_with_minus),
      equal_exprt(input_int, unary_minus_exprt(sum)));
    constraints.existential.push_back(a7);
  }
  return constraints;
}

string_constraint_generatort::parseint_argumentst
string_constraint_generatort::unpack_parseint_arguments(
  const function_application_exprt &f,
  const typet &target_int_type)
{
  PRECONDITION(f.arguments().size() == 1 || f.arguments().size() == 2);
  PRECONDITION(target_int_type.id() == ID_signedbv);
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);

  const exprt radix =
    f.arguments().size() == 1
      ? static_cast<exprt>(from_integer(10, target_int_type))
      : static_cast<exprt>(typecast_exprt(f.arguments()[1], target_int_type));
  // Most of the time we can evaluate radix as an integer. The value 0 is used
  // to indicate when we can't tell what the radix is.
  const unsigned long radix_ul = to_integer_or_default(radix, 0, ns);
  PRECONDITION((radix_ul >= 2 && radix_ul <= 36) || radix_ul == 0);

  const std::size_t max_string_length =
    max_printed_string_length(target_int_type, radix_ul);

  return {str, radix, radix_ul, max_string_length};
}

/// Check a string is a valid integer, using the same rules as Java
/// Integer.parseInt
///
/// Add axioms relating a boolean return value to being a valid integer
/// \param f: a function application with arguments refined_string `str` and
///   an optional integer for the radix
/// \return boolean expression indicating whether the string is a valid integer
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_is_valid_int(
  const function_application_exprt &f)
{
  irep_idt called_function = to_symbol_expr(f.function()).get_identifier();
  PRECONDITION(
    called_function == ID_cprover_string_is_valid_int_func ||
    called_function == ID_cprover_string_is_valid_long_func);
  const signedbv_typet target_int_type{static_cast<size_t>(
    called_function == ID_cprover_string_is_valid_int_func ? 32 : 64)};
  auto args = unpack_parseint_arguments(f, target_int_type);

  const typet &char_type =
    to_type_with_subtype(args.str.content().type()).subtype();
  const typecast_exprt radix_as_char(args.radix, char_type);
  const bool strict_formatting = false;

  /// \note the only thing stopping us from taking longer strings with many
  /// leading zeros is the axioms for correct number format
  auto conjuncts = get_conjuncts_for_correct_number_format(
    args.str,
    radix_as_char,
    args.radix_ul,
    args.max_string_length,
    strict_formatting);

  return {typecast_exprt{conjunction(conjuncts), f.type()}, {}};
}

/// Integer value represented by a string
///
/// Add axioms ensuring the value of the returned integer corresponds
/// to the value represented by `str`
/// \param f: a function application with arguments refined_string `str` and
///   an optional integer for the radix
/// \return integer expression equal to the value represented by `str`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_parse_int(
  const function_application_exprt &f)
{
  auto args = unpack_parseint_arguments(f, f.type());

  const typet &type = f.type();

  const symbol_exprt input_int = fresh_symbol("parsed_int", type);
  const bool strict_formatting = false;

  auto constraints2 = add_axioms_for_characters_in_integer_string(
    input_int,
    type,
    strict_formatting,
    args.str,
    args.max_string_length,
    args.radix,
    args.radix_ul);

  return {input_int, std::move(constraints2)};
}

/// Check if a character is a digit with respect to the given radix, e.g. if the
/// radix is 10 then check if the character is in the range 0-9.
/// \param chr: the character
/// \param strict_formatting: if true, don't allow upper case characters
/// \param radix_as_char: the radix as an expression of the same type as chr
/// \param radix_ul: the radix, which should be between 2 and 36, or 0, in
///   which case the return value will work for any radix
/// \return an expression for the condition
exprt is_digit_with_radix(
  const exprt &chr,
  const bool strict_formatting,
  const exprt &radix_as_char,
  const unsigned long radix_ul)
{
  PRECONDITION((radix_ul >= 2 && radix_ul <= 36) || radix_ul == 0);
  const typet &char_type = chr.type();
  const exprt zero_char = from_integer('0', char_type);

  const and_exprt is_digit_when_radix_le_10(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(chr, ID_lt, plus_exprt(zero_char, radix_as_char)));

  if(radix_ul <= 10 && radix_ul != 0)
  {
    return is_digit_when_radix_le_10;
  }
  else
  {
    const exprt nine_char = from_integer('9', char_type);
    const exprt a_char = from_integer('a', char_type);
    const constant_exprt ten_char_type = from_integer(10, char_type);

    const minus_exprt radix_minus_ten(radix_as_char, ten_char_type);

    or_exprt is_digit_when_radix_gt_10(
      and_exprt(
        binary_relation_exprt(chr, ID_ge, zero_char),
        binary_relation_exprt(chr, ID_le, nine_char)),
      and_exprt(
        binary_relation_exprt(chr, ID_ge, a_char),
        binary_relation_exprt(
          chr, ID_lt, plus_exprt(a_char, radix_minus_ten))));

    if(!strict_formatting)
    {
      exprt A_char = from_integer('A', char_type);
      is_digit_when_radix_gt_10.copy_to_operands(and_exprt(
        binary_relation_exprt(chr, ID_ge, A_char),
        binary_relation_exprt(
          chr, ID_lt, plus_exprt(A_char, radix_minus_ten))));
    }

    if(radix_ul == 0)
    {
      return if_exprt(
        binary_relation_exprt(radix_as_char, ID_le, ten_char_type),
        is_digit_when_radix_le_10,
        is_digit_when_radix_gt_10);
    }
    else
    {
      return std::move(is_digit_when_radix_gt_10);
    }
  }
}

/// Get the numeric value of a character, assuming that the radix is large
/// enough. '+' and '-' yield 0.
/// \param chr: the character to get the numeric value of
/// \param char_type: the type to use for characters
/// \param type: the type to use for the return value
/// \param strict_formatting: if true, don't allow upper case characters
/// \param radix_ul: the radix, which should be between 2 and 36, or 0, in
///   which case the return value will work for any radix
/// \return an integer expression of the given type with the numeric value of
///   the char
exprt get_numeric_value_from_character(
  const exprt &chr,
  const typet &char_type,
  const typet &type,
  const bool strict_formatting,
  const unsigned long radix_ul)
{
  const constant_exprt zero_char = from_integer('0', char_type);

  /// There are four cases, which occur in ASCII in the following order:
  /// '+' and '-', digits, upper case letters, lower case letters
  const binary_relation_exprt upper_case_lower_case_or_digit(
    chr, ID_ge, zero_char);

  if(radix_ul <= 10 && radix_ul != 0)
  {
    /// return char >= '0' ? (char - '0') : 0
    return typecast_exprt(
      if_exprt(
        upper_case_lower_case_or_digit,
        minus_exprt(chr, zero_char),
        from_integer(0, char_type)),
      type);
  }
  else
  {
    const constant_exprt a_char = from_integer('a', char_type);
    const binary_relation_exprt lower_case(chr, ID_ge, a_char);
    const constant_exprt A_char = from_integer('A', char_type);
    const binary_relation_exprt upper_case_or_lower_case(chr, ID_ge, A_char);
    const constant_exprt ten_int = from_integer(10, char_type);

    if(strict_formatting)
    {
      /// return char >= 'a' ? (char - 'a' + 10) :
      ///   char >= '0' ? (char - '0') : 0
      return typecast_exprt(
        if_exprt(
          lower_case,
          plus_exprt(minus_exprt(chr, a_char), ten_int),
          if_exprt(
            upper_case_lower_case_or_digit,
            minus_exprt(chr, zero_char),
            from_integer(0, char_type))),
        type);
    }
    else
    {
      /// return char >= 'a' ? (char - 'a' + 10) :
      ///   char >= 'A' ? (char - 'A' + 10) :
      ///     char >= '0' ? (char - '0') : 0
      return typecast_exprt(
        if_exprt(
          lower_case,
          plus_exprt(minus_exprt(chr, a_char), ten_int),
          if_exprt(
            upper_case_or_lower_case,
            plus_exprt(minus_exprt(chr, A_char), ten_int),
            if_exprt(
              upper_case_lower_case_or_digit,
              minus_exprt(chr, zero_char),
              from_integer(0, char_type)))),
        type);
    }
  }
}

/// Calculate the string length needed to represent any value of the given type
/// using the given radix. Due to floating point rounding errors we sometimes
/// return a value 1 larger than needed, which is fine for our purposes.
/// \param type: the type that we are considering values of
/// \param radix_ul: the radix we are using, or 0, in which case the return
///   value will work for any radix
/// \return the maximum string length
size_t max_printed_string_length(const typet &type, unsigned long radix_ul)
{
  if(radix_ul == 0)
  {
    radix_ul = 2;
  }
  double n_bits = static_cast<double>(to_bitvector_type(type).get_width());
  double radix = static_cast<double>(radix_ul);
  bool signed_type = type.id() == ID_signedbv;
  /// We want to calculate max, the maximum number of characters needed to
  /// represent any value of the given type.
  ///
  /// For signed types, the longest string will be for -2^(n_bits-1), so
  /// max = 1 + min{k: 2^(n_bits-1) < radix^k} (the 1 is for the minus sign)
  ///     = 1 + min{k: n_bits-1 < k log_2(radix)}
  ///     = 1 + min{k: k > (n_bits-1) / log_2(radix)}
  ///     = 1 + min{k: k > floor((n_bits-1) / log_2(radix))}
  ///     = 1 + (1 + floor((n_bits-1) / log_2(radix)))
  ///     = 2 + floor((n_bits-1) / log_2(radix))
  ///
  /// For unsigned types, the longest string will be for (2^n_bits)-1, so
  /// max = min{k: (2^n_bits)-1 < radix^k}
  ///     = min{k: 2^n_bits <= radix^k}
  ///     = min{k: n_bits <= k log_2(radix)}
  ///     = min{k: k >= n_bits / log_2(radix)}
  ///     = min{k: k >= ceil(n_bits / log_2(radix))}
  ///     = ceil(n_bits / log_2(radix))
  double max = signed_type
                 ? floor(static_cast<double>(n_bits - 1) / log2(radix)) + 2.0
                 : ceil(static_cast<double>(n_bits) / log2(radix));
  return static_cast<size_t>(max);
}
