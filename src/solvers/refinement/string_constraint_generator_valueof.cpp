/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions generating strings from other
///   types, in particular int, long, float, double, char, bool

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <util/simplify_expr.h>

#include <cmath>
#include <solvers/floatbv/float_bv.h>


/// Add axioms corresponding to the String.valueOf(I) java function.
/// \param expr: function application with one integer argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  PRECONDITION(expr.arguments().size()>=1);
  if(expr.arguments().size()==1)
  {
    return add_axioms_from_int(expr.arguments()[0], ref_type);
  }
  else
  {
    return add_axioms_from_int_with_radix(
      expr.arguments()[0],
      expr.arguments()[1],
      ref_type);
  }
}

/// Add axioms corresponding to the String.valueOf(J) java function.
/// \param expr: function application with one long argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_long(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  PRECONDITION(expr.arguments().size()>=1);
  if(expr.arguments().size()==1)
  {
    return add_axioms_from_int(expr.arguments()[0], ref_type);
  }
  else
  {
    return add_axioms_from_int_with_radix(
      expr.arguments()[0],
      expr.arguments()[1],
      ref_type);
  }
}

/// Add axioms corresponding to the String.valueOf(Z) java function.
/// \param f: function application with a Boolean argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_bool(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_bool(args(f, 1)[0], ref_type);
}

/// Add axioms stating that the returned string equals "true" when the Boolean
/// expression is true and "false" when it is false.
/// \param b: Boolean expression
/// \param ref_type: type of refined string expressions
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_bool(
  const exprt &b, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &char_type=ref_type.get_char_type();

  PRECONDITION(b.type()==bool_typet() || b.type().id()==ID_c_bool);

  typecast_exprt eq(b, bool_typet());

  // We add axioms:
  // a1 : eq => res = |"true"|
  // a2 : forall i < |"true"|. eq => res[i]="true"[i]
  // a3 : !eq => res = |"false"|
  // a4 : forall i < |"false"|. !eq => res[i]="false"[i]

  std::string str_true="true";
  implies_exprt a1(eq, res.axiom_for_has_length(str_true.length()));
  m_axioms.push_back(a1);

  for(std::size_t i=0; i<str_true.length(); i++)
  {
    exprt chr=from_integer(str_true[i], char_type);
    implies_exprt a2(eq, equal_exprt(res[i], chr));
    m_axioms.push_back(a2);
  }

  std::string str_false="false";
  implies_exprt a3(not_exprt(eq), res.axiom_for_has_length(str_false.length()));
  m_axioms.push_back(a3);

  for(std::size_t i=0; i<str_false.length(); i++)
  {
    exprt chr=from_integer(str_false[i], char_type);
    implies_exprt a4(not_exprt(eq), equal_exprt(res[i], chr));
    m_axioms.push_back(a4);
  }

  return res;
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(I) or String.valueOf(J) Java functions applied
/// on the integer expression.
/// \param x: a signed integer expression
/// \param ref_type: type for refined strings
/// \param max_size: a maximal size for the string representation (default 0,
///   which is interpreted to mean "as large as is needed for this type")
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const exprt &input_int,
  const refined_string_typet &ref_type,
  size_t max_size)
{
  const constant_exprt radix=from_integer(10, input_int.type());
  return add_axioms_from_int_with_radix(input_int, radix, ref_type, max_size);
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(II) or String.valueOf(JI) Java functions applied
/// on the integer expression.
/// \param input_int: a signed integer expression
/// \param radix: the radix to use
/// \param ref_type: type for refined strings
/// \param max_size: a maximal size for the string representation (default 0,
///   which is interpreted to mean "as large as is needed for this type")
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_from_int_with_radix(
  const exprt &input_int,
  const exprt &radix,
  const refined_string_typet &ref_type,
  size_t max_size)
{
  PRECONDITION(max_size==0 || max_size<std::numeric_limits<size_t>::max());
  const typet &type=input_int.type();
  PRECONDITION(type.id()==ID_signedbv);

  /// Most of the time we can evaluate radix as an integer. The value 0 is used
  /// to indicate when we can't tell what the radix is.
  const unsigned long radix_ul=to_integer_or_default(radix, 0);
  CHECK_RETURN((radix_ul>=2 && radix_ul<=36) || radix_ul==0);

  if(max_size==0)
  {
    max_size=max_printed_string_length(type, radix_ul);
    CHECK_RETURN(max_size<std::numeric_limits<size_t>::max());
  }

  string_exprt str=fresh_string(ref_type);
  const typet &char_type=ref_type.get_char_type();
  exprt radix_as_char=typecast_exprt(radix, char_type);
  exprt radix_input_type=typecast_exprt(radix, type);
  const bool strict_formatting=true;

  add_axioms_for_correct_number_format(
    input_int, str, radix_as_char, radix_ul, max_size, strict_formatting);

  add_axioms_for_characters_in_integer_string(
    input_int,
    type,
    strict_formatting,
    str,
    max_size,
    radix_input_type,
    radix_ul);

  return str;
}

/// Returns the integer value represented by the character.
/// \param chr: a character expression in the following set:
///   0123456789abcdef
/// \return an integer expression
exprt string_constraint_generatort::int_of_hex_char(const exprt &chr)
{
  exprt zero_char=constant_char('0', chr.type());
  exprt nine_char=constant_char('9', chr.type());
  exprt a_char=constant_char('a', chr.type());
  return if_exprt(
    binary_relation_exprt(chr, ID_gt, nine_char),
    plus_exprt(constant_char(10, chr.type()), minus_exprt(chr, a_char)),
    minus_exprt(chr, zero_char));
}

/// Add axioms stating that the returned string corresponds to the integer
/// argument written in hexadecimal.
/// \param i: an integer argument
/// \param ref_type: type of refined string expressions
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_int_hex(
  const exprt &i, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &type=i.type();
  PRECONDITION(type.id()==ID_signedbv);
  const typet &index_type=ref_type.get_index_type();
  const typet &char_type=ref_type.get_char_type();
  exprt sixteen=from_integer(16, index_type);
  exprt minus_char=constant_char('-', char_type);
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt a_char=constant_char('a', char_type);
  exprt f_char=constant_char('f', char_type);

  size_t max_size=8;
  m_axioms.push_back(
    and_exprt(res.axiom_for_length_gt(0),
              res.axiom_for_length_le(max_size)));

  for(size_t size=1; size<=max_size; size++)
  {
    exprt sum=from_integer(0, type);
    exprt all_numbers=true_exprt();
    exprt chr=res[0];

    for(size_t j=0; j<size; j++)
    {
      chr=res[j];
      exprt i=int_of_hex_char(chr);
      sum=plus_exprt(mult_exprt(sum, sixteen), typecast_exprt(i, type));
      or_exprt is_number(
        and_exprt(
          binary_relation_exprt(chr, ID_ge, zero_char),
          binary_relation_exprt(chr, ID_le, nine_char)),
        and_exprt(
          binary_relation_exprt(chr, ID_ge, a_char),
          binary_relation_exprt(chr, ID_le, f_char)));
      all_numbers=and_exprt(all_numbers, is_number);
    }

    equal_exprt premise(res.axiom_for_has_length(size));
    m_axioms.push_back(
      implies_exprt(premise, and_exprt(equal_exprt(i, sum), all_numbers)));

    // disallow 0s at the beginning
    if(size>1)
      m_axioms.push_back(
        implies_exprt(premise, not_exprt(equal_exprt(res[0], zero_char))));
  }
  return res;
}

/// add axioms corresponding to the Integer.toHexString(I) java function
/// \param f: function application with an integer argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_int_hex(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_int_hex(args(f, 1)[0], ref_type);
}

/// Add axioms corresponding to the String.valueOf(C) java function.
/// \param f: function application one char argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_char(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_char(args(f, 1)[0], ref_type);
}

/// Add axioms stating that the returned string has length 1 and the character
/// it contains corresponds to the input expression.
/// \param c: one expression of type char
/// \param ref_type: type of refined string expressions
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_char(
  const exprt &c, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  and_exprt lemma(equal_exprt(res[0], c), res.axiom_for_has_length(1));
  m_axioms.push_back(lemma);
  return res;
}

/// Add axioms making the return value true if the given string is a correct
/// number in the given radix
/// \param input_int: the number being represented as a string
/// \param str: string expression
/// \param radix_as_char: the radix as an expression of the same type as the
///   characters in str
/// \param radix_ul: the radix, which should be between 2 and 36, or 0, in
///   which case the return value will work for any radix
/// \param max_size: maximum number of characters
/// \param strict_formatting: if true, don't allow a leading plus, redundant
///   zeros or upper case letters
void string_constraint_generatort::add_axioms_for_correct_number_format(
  const exprt &input_int,
  const string_exprt &str,
  const exprt &radix_as_char,
  const unsigned long radix_ul,
  const std::size_t max_size,
  const bool strict_formatting)
{
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();

  const exprt &chr=str[0];
  const equal_exprt starts_with_minus(chr, constant_char('-', char_type));
  const equal_exprt starts_with_plus(chr, constant_char('+', char_type));
  const exprt starts_with_digit=
    is_digit_with_radix(chr, strict_formatting, radix_as_char, radix_ul);

  // |str| > 0
  const exprt non_empty=str.axiom_for_length_ge(from_integer(1, index_type));
  m_axioms.push_back(non_empty);

  if(strict_formatting)
  {
    // str[0] = '-' || is_digit_with_radix(str[0], radix)
    const or_exprt correct_first(starts_with_minus, starts_with_digit);
    m_axioms.push_back(correct_first);
  }
  else
  {
    // str[0] = '-' || str[0] = '+' || is_digit_with_radix(str[0], radix)
    const or_exprt correct_first(
      starts_with_minus, starts_with_digit, starts_with_plus);
    m_axioms.push_back(correct_first);
  }

  // str[0]='+' or '-' ==> |str| > 1
  const implies_exprt contains_digit(
    or_exprt(starts_with_minus, starts_with_plus),
    str.axiom_for_length_ge(from_integer(2, index_type)));
  m_axioms.push_back(contains_digit);

  // |str| <= max_size
  m_axioms.push_back(str.axiom_for_length_le(max_size));

  // forall 1 <= i < |str| . is_digit_with_radix(str[i], radix)
  // We unfold the above because we know that it will be used for all i up to
  // str.length(), and str.length() <= max_size
  for(std::size_t index=1; index<max_size; ++index)
  {
    /// index < length => is_digit_with_radix(str[index], radix)
    const implies_exprt character_at_index_is_digit(
      str.axiom_for_length_ge(from_integer(index+1, index_type)),
      is_digit_with_radix(
        str[index], strict_formatting, radix_as_char, radix_ul));
    m_axioms.push_back(character_at_index_is_digit);
  }

  if(strict_formatting)
  {
    const exprt zero_char=constant_char('0', char_type);

    // no_leading_zero : str[0] = '0' => |str| = 1
    const implies_exprt no_leading_zero(
      equal_exprt(chr, zero_char),
      str.axiom_for_has_length(from_integer(1, index_type)));
    m_axioms.push_back(no_leading_zero);

    // no_leading_zero_after_minus : str[0]='-' => str[1]!='0'
    implies_exprt no_leading_zero_after_minus(
      starts_with_minus, not_exprt(equal_exprt(str[1], zero_char)));
    m_axioms.push_back(no_leading_zero_after_minus);
  }
}

/// Add axioms connecting the characters in the input string to the value of the
/// output integer. It is constructive because it gives a formula for input_int
/// in terms of the characters in str.
/// \param input_int: the integer represented by str
/// \param type: the type for input_int
/// \param str: input string
/// \param max_string_length: the maximum length str can have
/// \param radix: the radix, with the same type as input_int
/// \param radix_ul: the radix as an unsigned long, or 0 if that can't be
///   determined
/// \param strict_formatting: if true, don't allow a leading plus, redundant
///   zeros or upper case letters
void string_constraint_generatort::add_axioms_for_characters_in_integer_string(
  const exprt &input_int,
  const typet &type,
  const bool strict_formatting,
  const string_exprt &str,
  const std::size_t max_string_length,
  const exprt &radix,
  const unsigned long radix_ul)
{
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();

  const equal_exprt starts_with_minus(str[0], constant_char('-', char_type));
  const constant_exprt zero_expr=from_integer(0, type);
  exprt::operandst digit_constraints;

  exprt sum=get_numeric_value_from_character(
    str[0], char_type, type, strict_formatting, radix_ul);

  /// Deal with size==1 case separately. There are axioms from
  /// add_axioms_for_correct_number_format which say that the string must
  /// contain at least one digit, so we don't have to worry about "+" or "-".
  m_axioms.push_back(
    implies_exprt(str.axiom_for_has_length(1), equal_exprt(input_int, sum)));

  for(size_t size=2; size<=max_string_length; size++)
  {
    // sum_0 := numeric value of res[0] (which is 0 if res[0] is '-')
    // For each 1<=j<max_string_length, we have:
    // sum_j := radix * sum_{j-1} + numeric value of res[j]
    // no_overflow_j := sum_{j-1} == (radix * sum_{j-1} / radix)
    //                  && sum_j >= sum_{j - 1}
    //   (the first part avoid overflows in the multiplication and the second
    //     one in the addition of the definition of sum_j)
    // For all 1<=size<=max_string_length we add axioms:
    // a5 : |res| == size =>
    //        forall max_string_length-2 <= j < size. no_overflow_j
    // a6 : |res| == size && res[0] is a digit for radix =>
    //        input_int == sum_{size-1}
    // a7 : |res| == size && res[0] == '-' => input_int == -sum_{size-1}

    const mult_exprt radix_sum(sum, radix);
    // new_sum = radix * sum + (numeric value of res[j])
    const exprt new_sum=plus_exprt(
      radix_sum,
      get_numeric_value_from_character(
        str[size-1], char_type, type, strict_formatting, radix_ul));

    // An overflow can happen when reaching the last index which can contain
    // a digit, which is `max_string_length - 2` because of the space left for
    // a minus sign. That assumes that we were able to identify the radix. If we
    // weren't then we check for overflow on every index.
    if(size-1>=max_string_length-2 || radix_ul==0)
    {
      const and_exprt no_overflow(
        equal_exprt(sum, div_exprt(radix_sum, radix)),
        binary_relation_exprt(new_sum, ID_ge, radix_sum));
      digit_constraints.push_back(no_overflow);
    }
    sum=new_sum;

    const equal_exprt premise=str.axiom_for_has_length(size);

    if(!digit_constraints.empty())
    {
      const implies_exprt a5(premise, conjunction(digit_constraints));
      m_axioms.push_back(a5);
    }

    const implies_exprt a6(
      and_exprt(premise, not_exprt(starts_with_minus)),
      equal_exprt(input_int, sum));
    m_axioms.push_back(a6);

    const implies_exprt a7(
      and_exprt(premise, starts_with_minus),
      equal_exprt(input_int, unary_minus_exprt(sum)));
    m_axioms.push_back(a7);
  }
}

/// add axioms corresponding to the Integer.parseInt java function
/// \param f: a function application with either one string expression or one
///   string expression and an integer expression for the radix
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_parse_int(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==1 || f.arguments().size()==2);
  const string_exprt str=get_string_expr(f.arguments()[0]);
  const typet &type=f.type();
  PRECONDITION(type.id()==ID_signedbv);
  const exprt radix=f.arguments().size()==1?
    static_cast<exprt>(from_integer(10, type)):
    static_cast<exprt>(typecast_exprt(f.arguments()[1], type));
  /// Most of the time we can evaluate radix as an integer. The value 0 is used
  /// to indicate when we can't tell what the radix is.
  const unsigned long radix_ul=to_integer_or_default(radix, 0);
  PRECONDITION((radix_ul>=2 && radix_ul<=36) || radix_ul==0);

  const symbol_exprt input_int=fresh_symbol("parsed_int", type);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typecast_exprt radix_as_char(radix, char_type);
  const bool strict_formatting=false;

  const std::size_t max_string_length=max_printed_string_length(type, radix_ul);

  /// TODO: we should throw an exception when this does not hold:
  /// Note that the only thing stopping us from taking longer strings with many
  /// leading zeros is the axioms for correct number format
  add_axioms_for_correct_number_format(
    input_int,
    str,
    radix_as_char,
    radix_ul,
    max_string_length,
    strict_formatting);

  add_axioms_for_characters_in_integer_string(
    input_int,
    type,
    strict_formatting,
    str,
    max_string_length,
    radix,
    radix_ul);

  return input_int;
}

/// If the expression is a constant expression then we get the value of it as
/// an unsigned long. If not we return a default value.
/// \param expr: input expression
/// \param def: default value to return if we cannot evaluate expr
/// \return the output as an unsigned long
unsigned long string_constraint_generatort::to_integer_or_default(
  const exprt &expr, unsigned long def)
{
  mp_integer mp_radix;
  bool to_integer_failed=to_integer(simplify_expr(expr, ns), mp_radix);
  return to_integer_failed?def:integer2ulong(mp_radix);
}

/// Check if a character is a digit with respect to the given radix, e.g. if the
/// radix is 10 then check if the character is in the range 0-9.
/// \param chr: the character
/// \param strict_formatting: if true, don't allow upper case characters
/// \param radix_as_char:  the radix as an expression of the same type as chr
/// \param radix_ul: the radix, which should be between 2 and 36, or 0, in
///   which case the return value will work for any radix
/// \return an expression for the condition
exprt is_digit_with_radix(
  const exprt &chr,
  const bool strict_formatting,
  const exprt &radix_as_char,
  const unsigned long radix_ul)
{
  PRECONDITION((radix_ul>=2 && radix_ul<=36) || radix_ul==0);
  const typet &char_type=chr.type();
  const exprt zero_char=from_integer('0', char_type);

  const and_exprt is_digit_when_radix_le_10(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(
      chr, ID_lt, plus_exprt(zero_char, radix_as_char)));

  if(radix_ul<=10 && radix_ul!=0)
  {
    return is_digit_when_radix_le_10;
  }
  else
  {
    const exprt nine_char=from_integer('9', char_type);
    const exprt a_char=from_integer('a', char_type);
    const constant_exprt ten_char_type=from_integer(10, char_type);

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
      exprt A_char=from_integer('A', char_type);
      is_digit_when_radix_gt_10.copy_to_operands(
        and_exprt(
          binary_relation_exprt(chr, ID_ge, A_char),
          binary_relation_exprt(
            chr, ID_lt, plus_exprt(A_char, radix_minus_ten))));
    }

    if(radix_ul==0)
    {
      return if_exprt(
        binary_relation_exprt(radix_as_char, ID_le, ten_char_type),
        is_digit_when_radix_le_10,
        is_digit_when_radix_gt_10);
    }
    else
    {
      return is_digit_when_radix_gt_10;
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
  const constant_exprt zero_char=from_integer('0', char_type);

  /// There are four cases, which occur in ASCII in the following order:
  /// '+' and '-', digits, upper case letters, lower case letters
  const binary_relation_exprt upper_case_lower_case_or_digit(
    chr, ID_ge, zero_char);

  if(radix_ul<=10 && radix_ul!=0)
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
    const constant_exprt a_char=from_integer('a', char_type);
    const binary_relation_exprt lower_case(chr, ID_ge, a_char);
    const constant_exprt A_char=from_integer('A', char_type);
    const binary_relation_exprt upper_case_or_lower_case(chr, ID_ge, A_char);
    const constant_exprt ten_int=from_integer(10, char_type);

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
  if(radix_ul==0)
  {
    radix_ul=2;
  }
  double n_bits=static_cast<double>(to_bitvector_type(type).get_width());
  double radix=static_cast<double>(radix_ul);
  bool signed_type=type.id()==ID_signedbv;
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
  double max=signed_type?
    floor(static_cast<double>(n_bits-1)/log2(radix))+2.0:
    ceil(static_cast<double>(n_bits)/log2(radix));
  return static_cast<size_t>(max);
}
