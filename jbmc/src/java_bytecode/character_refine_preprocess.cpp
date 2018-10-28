/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

/// \file
/// Preprocess a goto-programs so that calls to the java Character library are
///   replaced by simple expressions.

#include "character_refine_preprocess.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

/// converts based on a function on expressions
/// \param expr_function: A reference to a function on expressions
/// \param target: A position in a goto program
codet character_refine_preprocesst::convert_char_function(
  exprt (*expr_function)(const exprt &chr, const typet &type),
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==1);
  const exprt &arg=function_call.arguments()[0];
  const exprt &result=function_call.lhs();
  const typet &type=result.type();
  return code_assignt(result, expr_function(arg, type));
}

/// The returned expression is true when the first argument is in the interval
/// defined by the lower and upper bounds (included)
/// \param chr: Expression we want to bound
/// \param lower_bound: Integer lower bound
/// \param upper_bound: Integer upper bound
/// \return A Boolean expression
exprt character_refine_preprocesst::in_interval_expr(
  const exprt &chr,
  const mp_integer &lower_bound,
  const mp_integer &upper_bound)
{
  return and_exprt(
    binary_relation_exprt(chr, ID_ge, from_integer(lower_bound, chr.type())),
    binary_relation_exprt(chr, ID_le, from_integer(upper_bound, chr.type())));
}

/// The returned expression is true when the given character is equal to one of
/// the element in the list
/// \param chr: An expression of type character
/// \param list: A list of integer representing unicode characters
/// \return A Boolean expression
exprt character_refine_preprocesst::in_list_expr(
  const exprt &chr, const std::list<mp_integer> &list)
{
  exprt::operandst ops;
  for(const auto &i : list)
    ops.push_back(equal_exprt(chr, from_integer(i, chr.type())));
  return disjunction(ops);
}

/// Determines the number of char values needed to represent the specified
/// character (Unicode code point).
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A integer expression of the given type
exprt character_refine_preprocesst::expr_of_char_count(
  const exprt &chr, const typet &type)
{
  exprt u010000=from_integer(0x010000, type);
  binary_relation_exprt small(chr, ID_lt, u010000);
  return if_exprt(small, from_integer(1, type), from_integer(2, type));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.charCount:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_char_count(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_char_count, target);
}

/// Casts the given expression to the given type
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_char_value(
  const exprt &chr, const typet &type)
{
  return typecast_exprt(chr, type);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.charValue:()C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_char_value(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_char_value, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.compare:(CC)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_compare(conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==2);
  const exprt &char1=function_call.arguments()[0];
  const exprt &char2=function_call.arguments()[1];
  const exprt &result=function_call.lhs();
  const typet &type=result.type();
  binary_relation_exprt smaller(char1, ID_lt, char2);
  binary_relation_exprt greater(char1, ID_gt, char2);
  if_exprt expr(
    smaller,
    from_integer(-1, type),
    if_exprt(greater, from_integer(1, type), from_integer(0, type)));

  return code_assignt(result, expr);
}


/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.digit:(CI)I. The function call has one character
/// argument and an optional integer radix argument. If the radix is not given
/// it is set to 36 by default.
/// \param target: a position in a goto program
/// \return code assigning the result of the Character.digit function to the
///         left-hand-side of the given target
codet character_refine_preprocesst::convert_digit_char(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  const std::size_t nb_args=function_call.arguments().size();
  PRECONDITION(nb_args==1 || nb_args==2);
  const exprt &arg=function_call.arguments()[0];
  // If there is no radix argument we set it to 36 which is the maximum possible
  const exprt &radix=
    nb_args>1?function_call.arguments()[1]:from_integer(36, arg.type());
  const exprt &result=function_call.lhs();
  const typet &type=result.type();

  // TODO: If the radix is not in the range MIN_RADIX <= radix <= MAX_RADIX or
  // if the value of ch is not a valid digit in the specified radix,
  // -1 is returned.

  // Case 1: The method isDigit is true of the character and the Unicode
  // decimal digit value of the character (or its single-character
  // decomposition) is less than the specified radix.
  exprt invalid=from_integer(-1, arg.type());
  exprt c0=from_integer('0', arg.type());
  exprt latin_digit=in_interval_expr(arg, '0', '9');
  minus_exprt value1(arg, c0);
  // TODO: this is only valid for latin digits
  if_exprt case1(
    binary_relation_exprt(value1, ID_lt, radix), value1, invalid);

  // Case 2: The character is one of the uppercase Latin letters 'A'
  // through 'Z' and its code is less than radix + 'A' - 10,
  // then ch - 'A' + 10 is returned.
  exprt cA=from_integer('A', arg.type());
  exprt i10=from_integer(10, arg.type());
  exprt upper_case=in_interval_expr(arg, 'A', 'Z');
  plus_exprt value2(minus_exprt(arg, cA), i10);
  if_exprt case2(
    binary_relation_exprt(value2, ID_lt, radix), value2, invalid);

  // The character is one of the lowercase Latin letters 'a' through 'z' and
  // its code is less than radix + 'a' - 10, then ch - 'a' + 10 is returned.
  exprt ca=from_integer('a', arg.type());
  exprt lower_case=in_interval_expr(arg, 'a', 'z');
  plus_exprt value3(minus_exprt(arg, ca), i10);
  if_exprt case3(
    binary_relation_exprt(value3, ID_lt, radix), value3, invalid);


  // The character is one of the fullwidth uppercase Latin letters A ('\uFF21')
  // through Z ('\uFF3A') and its code is less than radix + '\uFF21' - 10.
  // In this case, ch - '\uFF21' + 10 is returned.
  exprt uFF21=from_integer(0xFF21, arg.type());
  exprt fullwidth_upper_case=in_interval_expr(arg, 0xFF21, 0xFF3A);
  plus_exprt value4(minus_exprt(arg, uFF21), i10);
  if_exprt case4(
    binary_relation_exprt(value4, ID_lt, radix), value4, invalid);

  // The character is one of the fullwidth lowercase Latin letters a ('\uFF41')
  // through z ('\uFF5A') and its code is less than radix + '\uFF41' - 10.
  // In this case, ch - '\uFF41' + 10 is returned.
  exprt uFF41=from_integer(0xFF41, arg.type());
  plus_exprt value5(minus_exprt(arg, uFF41), i10);
  if_exprt case5(
    binary_relation_exprt(value5, ID_lt, radix), value5, invalid);

  if_exprt fullwidth_cases(fullwidth_upper_case, case4, case5);
  if_exprt expr(
    latin_digit,
    case1,
    if_exprt(upper_case, case2, if_exprt(lower_case, case3, fullwidth_cases)));
  typecast_exprt tc_expr(expr, type);

  return code_assignt(result, tc_expr);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.digit:(II)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_digit_int(conversion_inputt &target)
{
  return convert_digit_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.forDigit:(II)C
///
///    TODO: For now the radix argument is ignored
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_for_digit(conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==2);
  const exprt &digit=function_call.arguments()[0];
  const exprt &result=function_call.lhs();
  const typet &type=result.type();
  typecast_exprt casted_digit(digit, type);

  exprt d10=from_integer(10, type);
  binary_relation_exprt small(casted_digit, ID_le, d10);
  plus_exprt value1(casted_digit, from_integer('0', type));
  plus_exprt value2(minus_exprt(casted_digit, d10), from_integer('a', type));
  return code_assignt(result, if_exprt(small, value1, value2));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getDirectionality:(C)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_get_directionality_char(
  conversion_inputt &target)
{
  // TODO: This is unimplemented for now as it requires analyzing
  // the UnicodeData file to find characters directionality.
  return target;
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getDirectionality:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_get_directionality_int(
  conversion_inputt &target)
{
  return convert_get_directionality_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getNumericValue:(C)I
///
///    TODO: For now this is only for ASCII characters
codet character_refine_preprocesst::convert_get_numeric_value_char(
  conversion_inputt &target)
{
  return convert_digit_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getNumericValue:(C)I
///
///    TODO: For now this is only for ASCII characters
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_get_numeric_value_int(
  conversion_inputt &target)
{
  return convert_digit_int(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getType:(C)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_get_type_char(
  conversion_inputt &target)
{
  // TODO: This is unimplemented for now as it requires analyzing
  // the UnicodeData file to categorize characters.
  return target;
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.getType:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_get_type_int(
  conversion_inputt &target)
{
  return convert_get_type_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.hashCode:()I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_hash_code(conversion_inputt &target)
{
  return convert_char_value(target);
}

/// Returns the leading surrogate (a high surrogate code unit) of the surrogate
/// pair representing the specified supplementary character (Unicode code point)
/// in the UTF-16 encoding.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_high_surrogate(
  const exprt &chr, const typet &type)
{
  exprt u10000=from_integer(0x010000, type);
  exprt uD800=from_integer(0xD800, type);
  exprt u400=from_integer(0x0400, type);

  plus_exprt high_surrogate(uD800, div_exprt(minus_exprt(chr, u10000), u400));
  return std::move(high_surrogate);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.highSurrogate:(C)Z
codet character_refine_preprocesst::convert_high_surrogate(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_high_surrogate, target);
}

/// Determines if the specified character is an ASCII lowercase character.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_ascii_lower_case(
  const exprt &chr, const typet &type)
{
  return in_interval_expr(chr, 'a', 'z');
}

/// Determines if the specified character is an ASCII uppercase character.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_ascii_upper_case(
  const exprt &chr, const typet &type)
{
  return in_interval_expr(chr, 'A', 'Z');
}

/// Determines if the specified character is a letter.
///
///    TODO: for now this is only for ASCII characters, the
///          following unicode categories are not yet considered:
///          TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_letter(
  const exprt &chr, const typet &type)
{
  return or_exprt(
    expr_of_is_ascii_upper_case(chr, type),
    expr_of_is_ascii_lower_case(chr, type));
}

/// Determines if the specified character (Unicode code point) is alphabetic.
///
///    TODO: for now this is only for ASCII characters, the
///          following unicode categorise are not yet considered:
///          TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER
///          and contributory property Other_Alphabetic as defined by the
///          Unicode Standard.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_alphabetic(
  const exprt &chr, const typet &type)
{
  return expr_of_is_letter(chr, type);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isAlphabetic:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_alphabetic(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_alphabetic, target);
}

/// Determines whether the specified character (Unicode code point) is in the
/// Basic Multilingual Plane (BMP). Such code points can be represented using a
/// single char.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_bmp_code_point(
  const exprt &chr, const typet &type)
{
  return and_exprt(
    binary_relation_exprt(chr, ID_le, from_integer(0xFFFF, chr.type())),
    binary_relation_exprt(chr, ID_ge, from_integer(0, chr.type())));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isBmpCodePoint:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_bmp_code_point(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_bmp_code_point, target);
}

/// Determines if a character is defined in Unicode.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_defined(
  const exprt &chr, const typet &type)
{
  // The following intervals are undefined in unicode, according to
  // the Unicode Character Database: http://www.unicode.org/Public/UCD/latest/
  exprt::operandst intervals;
  intervals.push_back(in_interval_expr(chr, 0x0750, 0x077F));
  intervals.push_back(in_interval_expr(chr, 0x07C0, 0x08FF));
  intervals.push_back(in_interval_expr(chr, 0x1380, 0x139F));
  intervals.push_back(in_interval_expr(chr, 0x18B0, 0x18FF));
  intervals.push_back(in_interval_expr(chr, 0x1980, 0x19DF));
  intervals.push_back(in_interval_expr(chr, 0x1A00, 0x1CFF));
  intervals.push_back(in_interval_expr(chr, 0x1D80, 0x1DFF));
  intervals.push_back(in_interval_expr(chr, 0x2C00, 0x2E7F));
  intervals.push_back(in_interval_expr(chr, 0x2FE0, 0x2FEF));
  intervals.push_back(in_interval_expr(chr, 0x31C0, 0x31EF));
  intervals.push_back(in_interval_expr(chr, 0x9FB0, 0x9FFF));
  intervals.push_back(in_interval_expr(chr, 0xA4D0, 0xABFF));
  intervals.push_back(in_interval_expr(chr, 0xD7B0, 0xD7FF));
  intervals.push_back(in_interval_expr(chr, 0xFE10, 0xFE1F));
  intervals.push_back(in_interval_expr(chr, 0x10140, 0x102FF));
  intervals.push_back(in_interval_expr(chr, 0x104B0, 0x107FF));
  intervals.push_back(in_interval_expr(chr, 0x10840, 0x1CFFF));
  intervals.push_back(in_interval_expr(chr, 0x1D200, 0x1D2FF));
  intervals.push_back(in_interval_expr(chr, 0x1D360, 0x1D3FF));
  intervals.push_back(
    binary_relation_exprt(chr, ID_ge, from_integer(0x1D800, chr.type())));

  return not_exprt(disjunction(intervals));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isDefined:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_defined_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_defined, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isDefined:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_defined_int(
  conversion_inputt &target)
{
  return convert_is_defined_char(target);
}

/// Determines if the specified character is a digit. A character is a digit if
/// its general category type, provided by Character.getType(ch), is
/// DECIMAL_DIGIT_NUMBER.
///
///   TODO: for now we only support these ranges of digits:
///         '\\u0030' through '\\u0039', ISO-LATIN-1 digits ('0' through '9')
///         '\\u0660' through '\\u0669', Arabic-Indic digits
///         '\\u06F0' through '\\u06F9', Extended Arabic-Indic digits
///         '\\u0966' through '\\u096F', Devanagari digits
///         '\\uFF10' through '\\uFF19', Fullwidth digits
///         Many other character ranges contain digits as well.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_digit(
  const exprt &chr, const typet &type)
{
  exprt latin_digit=in_interval_expr(chr, '0', '9');
  exprt arabic_indic_digit=in_interval_expr(chr, 0x660, 0x669);
  exprt extended_digit=in_interval_expr(chr, 0x6F0, 0x6F9);
  exprt devanagari_digit=in_interval_expr(chr, 0x966, 0x96F);
  exprt fullwidth_digit=in_interval_expr(chr, 0xFF10, 0xFF19);
  or_exprt digit(
    or_exprt(latin_digit, or_exprt(arabic_indic_digit, extended_digit)),
    or_exprt(devanagari_digit, fullwidth_digit));
  return std::move(digit);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isDigit:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_digit_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.digit:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_digit_int(
  conversion_inputt &target)
{
  return convert_is_digit_char(target);
}

/// Determines if the given char value is a Unicode high-surrogate code unit
/// (also known as leading-surrogate code unit).
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_high_surrogate(
  const exprt &chr, const typet &type)
{
  return in_interval_expr(chr, 0xD800, 0xDBFF);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isHighSurrogate:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_high_surrogate(
    conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_high_surrogate, target);
}

/// Determines if the character is one of ignorable in a Java identifier, that
/// is, it is in one of these ranges: '\\u0000' through '\\u0008' '\\u000E'
/// through '\\u001B' '\\u007F' through '\\u009F'
///
///    TODO: For now, we ignore the FORMAT general category value
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_identifier_ignorable(
  const exprt &chr, const typet &type)
{
  or_exprt ignorable(
    in_interval_expr(chr, 0x0000, 0x0008),
     or_exprt(
      in_interval_expr(chr, 0x000E, 0x001B),
      in_interval_expr(chr, 0x007F, 0x009F)));
  return std::move(ignorable);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isIdentifierIgnorable:(C)Z
///
///    TODO: For now, we ignore the FORMAT general category value
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_identifier_ignorable_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_identifier_ignorable, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isIdentifierIgnorable:(I)Z
///
///    TODO: For now, we ignore the FORMAT general category value
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_identifier_ignorable_int(
  conversion_inputt &target)
{
  return convert_is_identifier_ignorable_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isIdeographic:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_ideographic(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==1);
  const exprt &arg=function_call.arguments()[0];
  const exprt &result=function_call.lhs();
  exprt is_ideograph=in_interval_expr(arg, 0x4E00, 0x9FFF);
  return code_assignt(result, is_ideograph);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isISOControl:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_ISO_control_char(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==1);
  const exprt &arg=function_call.arguments()[0];
  const exprt &result=function_call.lhs();
  or_exprt iso(
    in_interval_expr(arg, 0x00, 0x1F), in_interval_expr(arg, 0x7F, 0x9F));
  return code_assignt(result, iso);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isISOControl:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_ISO_control_int(
  conversion_inputt &target)
{
  return convert_is_ISO_control_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isJavaIdentifierPart:(C)Z
///
///    TODO: For now we do not allow currency symbol, connecting punctuation,
///          combining mark, non-spacing mark
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_identifier_part_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_unicode_identifier_part, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method isJavaIdentifierPart:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_identifier_part_int(
  conversion_inputt &target)
{
  return convert_is_unicode_identifier_part_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method isJavaIdentifierStart:(C)Z
///
///    TODO: For now we only allow letters and letter numbers.
///          The java specification for this function is not precise on the
///          other characters.
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_identifier_start_char(
    conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_unicode_identifier_start, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method isJavaIdentifierStart:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_identifier_start_int(
  conversion_inputt &target)
{
  return convert_is_java_identifier_start_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isJavaLetter:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_letter(
    conversion_inputt &target)
{
  return convert_is_java_identifier_start_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method isJavaLetterOrDigit:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_java_letter_or_digit(
  conversion_inputt &target)
{
  return convert_is_java_identifier_part_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLetter:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_letter_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_letter, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLetter:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_letter_int(
  conversion_inputt &target)
{
  return convert_is_letter_char(target);
}

/// Determines if the specified character is a letter or digit.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_letter_or_digit(
  const exprt &chr, const typet &type)
{
  return or_exprt(expr_of_is_letter(chr, type), expr_of_is_digit(chr, type));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLetterOrDigit:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_letter_or_digit_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLetterOrDigit:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_letter_or_digit_int(
  conversion_inputt &target)
{
  return convert_is_letter_or_digit_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLowerCase:(C)Z
///
///    TODO: For now we only consider ASCII characters
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_lower_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_ascii_lower_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLowerCase:(I)Z
///
///    TODO: For now we only consider ASCII characters
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_lower_case_int(
  conversion_inputt &target)
{
  return convert_is_lower_case_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isLowSurrogate:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_low_surrogate(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==1);
  const exprt &arg=function_call.arguments()[0];
  const exprt &result=function_call.lhs();
  exprt is_low_surrogate=in_interval_expr(arg, 0xDC00, 0xDFFF);
  return code_assignt(result, is_low_surrogate);
}

/// Determines whether the character is mirrored according to the Unicode
/// specification.
///
///    TODO: For now only ASCII characters are considered
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_is_mirrored(
  const exprt &chr, const typet &type)
{
  return in_list_expr(chr, {0x28, 0x29, 0x3C, 0x3E, 0x5B, 0x5D, 0x7B, 0x7D});
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isMirrored:(C)Z
///
///    TODO: For now only ASCII characters are considered
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_mirrored_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_mirrored, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isMirrored:(I)Z
///
///    TODO: For now only ASCII characters are considered
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_mirrored_int(
  conversion_inputt &target)
{
  return convert_is_mirrored_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSpace:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_space(conversion_inputt &target)
{
  return convert_is_whitespace_char(target);
}

/// Determines if the specified character is white space according to Unicode
/// (SPACE_SEPARATOR, LINE_SEPARATOR, or PARAGRAPH_SEPARATOR)
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_space_char(
  const exprt &chr, const typet &type)
{
  std::list<mp_integer> space_characters=
    {0x20, 0x00A0, 0x1680, 0x202F, 0x205F, 0x3000, 0x2028, 0x2029};
  exprt condition0=in_list_expr(chr, space_characters);
  exprt condition1=in_interval_expr(chr, 0x2000, 0x200A);
  return or_exprt(condition0, condition1);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSpaceChar:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_space_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_space_char, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSpaceChar:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_space_char_int(
  conversion_inputt &target)
{
  return convert_is_space_char(target);
}

/// Determines whether the specified character (Unicode code point) is in the
/// supplementary character range.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_supplementary_code_point(
  const exprt &chr, const typet &type)
{
  return binary_relation_exprt(chr, ID_gt, from_integer(0xFFFF, chr.type()));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSupplementaryCodePoint:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_supplementary_code_point(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_supplementary_code_point, target);
}

/// Determines if the given char value is a Unicode surrogate code unit.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_surrogate(
  const exprt &chr, const typet &type)
{
  return in_interval_expr(chr, 0xD800, 0xDFFF);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSurrogate:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_surrogate(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_surrogate, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isSurrogatePair:(CC)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_surrogate_pair(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==2);
  const exprt &arg0=function_call.arguments()[0];
  const exprt &arg1=function_call.arguments()[1];
  const exprt &result=function_call.lhs();
  exprt is_low_surrogate=in_interval_expr(arg1, 0xDC00, 0xDFFF);
  exprt is_high_surrogate=in_interval_expr(arg0, 0xD800, 0xDBFF);
  return code_assignt(result, and_exprt(is_high_surrogate, is_low_surrogate));
}

/// Determines if the specified character is a titlecase character.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_title_case(
  const exprt &chr, const typet &type)
{
  std::list<mp_integer>title_case_chars=
    {0x01C5, 0x01C8, 0x01CB, 0x01F2, 0x1FBC, 0x1FCC, 0x1FFC};
  exprt::operandst conditions;
  conditions.push_back(in_list_expr(chr, title_case_chars));
  conditions.push_back(in_interval_expr(chr, 0x1F88, 0x1F8F));
  conditions.push_back(in_interval_expr(chr, 0x1F98, 0x1F9F));
  conditions.push_back(in_interval_expr(chr, 0x1FA8, 0x1FAF));
  return disjunction(conditions);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isTitleCase:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_title_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_title_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isTitleCase:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_title_case_int(
  conversion_inputt &target)
{
  return convert_is_title_case_char(target);
}

/// Determines if the specified character is in the LETTER_NUMBER category of
/// Unicode
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_letter_number(
  const exprt &chr, const typet &type)
{
  // The following set of characters is the general category "Nl" in the
  // Unicode specification.
  exprt cond0=in_interval_expr(chr, 0x16EE, 0x16F0);
  exprt cond1=in_interval_expr(chr, 0x2160, 0x2188);
  exprt cond2=in_interval_expr(chr, 0x3021, 0x3029);
  exprt cond3=in_interval_expr(chr, 0x3038, 0x303A);
  exprt cond4=in_interval_expr(chr, 0xA6E6, 0xA6EF);
  exprt cond5=in_interval_expr(chr, 0x10140, 0x10174);
  exprt cond6=in_interval_expr(chr, 0x103D1, 0x103D5);
  exprt cond7=in_interval_expr(chr, 0x12400, 0x1246E);
  exprt cond8=in_list_expr(chr, {0x3007, 0x10341, 0x1034A});
  return or_exprt(
    or_exprt(or_exprt(cond0, cond1), or_exprt(cond2, cond3)),
    or_exprt(or_exprt(cond4, cond5), or_exprt(cond6, or_exprt(cond7, cond8))));
}


/// Determines if the character may be part of a Unicode identifier.
///
///    TODO: For now we do not allow connecting punctuation, combining mark,
///          non-spacing mark
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_unicode_identifier_part(
  const exprt &chr, const typet &type)
{
  exprt::operandst conditions;
  conditions.push_back(expr_of_is_unicode_identifier_start(chr, type));
  conditions.push_back(expr_of_is_digit(chr, type));
  conditions.push_back(expr_of_is_identifier_ignorable(chr, type));
  return disjunction(conditions);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUnicodeIdentifierPart:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_unicode_identifier_part_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_unicode_identifier_part, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUnicodeIdentifierPart:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_unicode_identifier_part_int(
  conversion_inputt &target)
{
  return convert_is_unicode_identifier_part_char(target);
}

/// Determines if the specified character is permissible as the first character
/// in a Unicode identifier.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_unicode_identifier_start(
  const exprt &chr, const typet &type)
{
  return or_exprt(
    expr_of_is_letter(chr, type), expr_of_is_letter_number(chr, type));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUnicodeIdentifierStart:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_unicode_identifier_start_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_unicode_identifier_start, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUnicodeIdentifierStart:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_unicode_identifier_start_int(
  conversion_inputt &target)
{
  return convert_is_unicode_identifier_start_char(target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUpperCase:(C)Z
///
///    TODO: For now we only consider ASCII characters
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_upper_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_ascii_upper_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isUpperCase:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_upper_case_int(
  conversion_inputt &target)
{
  return convert_is_upper_case_char(target);
}

/// Determines whether the specified code point is a valid Unicode code point
/// value. That is, in the range of integers from 0 to 0x10FFFF
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_valid_code_point(
  const exprt &chr, const typet &type)
{
  return binary_relation_exprt(chr, ID_le, from_integer(0x10FFFF, chr.type()));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isValidCodePoint:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_valid_code_point(
    conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_valid_code_point, target);
}

/// Determines if the specified character is white space according to Java. It
/// is the case when it one of the following: * a Unicode space character
/// (SPACE_SEPARATOR, LINE_SEPARATOR, or PARAGRAPH_SEPARATOR) but is not also a
/// non-breaking space ('\\u00A0', '\\u2007', '\\u202F'). * it is one of these:
/// U+0009  U+000A U+000B U+000C U+000D U+001C U+001D U+001E U+001F
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A Boolean expression
exprt character_refine_preprocesst::expr_of_is_whitespace(
  const exprt &chr, const typet &type)
{
  exprt::operandst conditions;
  std::list<mp_integer> space_characters=
    {0x20, 0x1680, 0x205F, 0x3000, 0x2028, 0x2029};
  conditions.push_back(in_list_expr(chr, space_characters));
  conditions.push_back(in_interval_expr(chr, 0x2000, 0x2006));
  conditions.push_back(in_interval_expr(chr, 0x2008, 0x200A));
  conditions.push_back(in_interval_expr(chr, 0x09, 0x0D));
  conditions.push_back(in_interval_expr(chr, 0x1C, 0x1F));
  return disjunction(conditions);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isWhitespace:(C)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_whitespace_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_is_whitespace, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.isWhitespace:(I)Z
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_is_whitespace_int(
  conversion_inputt &target)
{
  return convert_is_whitespace_char(target);
}

/// Returns the trailing surrogate (a low surrogate code unit) of the surrogate
/// pair representing the specified supplementary character (Unicode code point)
/// in the UTF-16 encoding.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A integer expression of the given type
exprt character_refine_preprocesst::expr_of_low_surrogate(
  const exprt &chr, const typet &type)
{
  exprt uDC00=from_integer(0xDC00, type);
  exprt u0400=from_integer(0x0400, type);
  return plus_exprt(uDC00, mod_exprt(chr, u0400));
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.lowSurrogate:(I)C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_low_surrogate(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_low_surrogate, target);
}

/// Returns the value obtained by reversing the order of the bytes in the
/// specified char value.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A character expression of the given type
exprt character_refine_preprocesst::expr_of_reverse_bytes(
  const exprt &chr, const typet &type)
{
  shl_exprt first_byte(chr, from_integer(8, type));
  lshr_exprt second_byte(chr, from_integer(8, type));
  return plus_exprt(first_byte, second_byte);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.reverseBytes:(C)C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_reverse_bytes(
    conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_reverse_bytes, target);
}

/// Converts the specified character (Unicode code point) to its UTF-16
/// representation stored in a char array. If the specified code point is a BMP
/// (Basic Multilingual Plane or Plane 0) value, the resulting char array has
/// the same value as codePoint. If the specified code point is a supplementary
/// code point, the resulting char array has the corresponding surrogate pair.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return A character array expression of the given type
exprt character_refine_preprocesst::expr_of_to_chars(
  const exprt &chr, const typet &type)
{
  array_typet array_type=to_array_type(type);
  const typet &char_type=array_type.subtype();
  array_exprt case1(array_type);
  array_exprt case2(array_type);
  exprt low_surrogate=expr_of_low_surrogate(chr, char_type);
  case1.copy_to_operands(low_surrogate);
  case2.move_to_operands(low_surrogate);
  exprt high_surrogate=expr_of_high_surrogate(chr, char_type);
  case2.move_to_operands(high_surrogate);
  return if_exprt(expr_of_is_bmp_code_point(chr, type), case1, case2);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toChars:(I)[C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_chars(conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_to_chars, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toCodePoint:(CC)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_code_point(
  conversion_inputt &target)
{
  const code_function_callt &function_call=target;
  assert(function_call.arguments().size()==2);
  const exprt &arg0=function_call.arguments()[0];
  const exprt &arg1=function_call.arguments()[1];
  const exprt &result=function_call.lhs();
  const typet &type=result.type();

  // These operations implement the decoding of a unicode symbol encoded
  // in UTF16 for the supplementary planes (above U+10000).
  // The low ten bits of the first character give the bits 10 to 19 of
  // code point and the low ten bits of the second give the bits 0 to 9,
  // then 0x10000 is added to the result. For more explenations see:
  //   https://en.wikipedia.org/wiki/UTF-16

  exprt u010000=from_integer(0x010000, type);
  exprt mask10bit=from_integer(0x03FF, type);
  shl_exprt m1(bitand_exprt(arg0, mask10bit), from_integer(10, type));
  bitand_exprt m2(arg1, mask10bit);
  bitor_exprt pair_value(u010000, bitor_exprt(m1, m2));
  return code_assignt(result, pair_value);
}

/// Converts the character argument to lowercase.
///
///    TODO: For now we only consider ASCII characters but ultimately
///          we should use case mapping information from the
///          UnicodeData file
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_to_lower_case(
  const exprt &chr, const typet &type)
{
  minus_exprt transformed(
    plus_exprt(chr, from_integer('a', type)), from_integer('A', type));

  if_exprt res(expr_of_is_ascii_upper_case(chr, type), transformed, chr);
  return std::move(res);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toLowerCase:(C)C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_lower_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_to_lower_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toLowerCase:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_lower_case_int(
  conversion_inputt &target)
{
  return convert_to_lower_case_char(target);
}

/// Converts the character argument to titlecase.
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_to_title_case(
  const exprt &chr, const typet &type)
{
  std::list<mp_integer> increment_list={0x01C4, 0x01C7, 0x01CA, 0x01F1};
  std::list<mp_integer> decrement_list={0x01C6, 0x01C9, 0x01CC, 0x01F3};
  exprt plus_8_interval1=in_interval_expr(chr, 0x1F80, 0x1F87);
  exprt plus_8_interval2=in_interval_expr(chr, 0x1F90, 0x1F97);
  exprt plus_8_interval3=in_interval_expr(chr, 0x1FA0, 0x1FA7);
  std::list<mp_integer> plus_9_list={0x1FB3, 0x1FC3, 0x1FF3};
  minus_exprt minus_1(chr, from_integer(1, type));
  plus_exprt plus_1(chr, from_integer(1, type));
  plus_exprt plus_8(chr, from_integer(8, type));
  plus_exprt plus_9(chr, from_integer(9, type));
  or_exprt plus_8_set(
    plus_8_interval1, or_exprt(plus_8_interval2, plus_8_interval3));

  if_exprt res(
    in_list_expr(chr, increment_list),
    plus_1,
    if_exprt(
      in_list_expr(chr, decrement_list),
      minus_1,
      if_exprt(
        plus_8_set,
        plus_8,
        if_exprt(
          in_list_expr(chr, plus_9_list),
          plus_9,
          chr))));

  return std::move(res);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toTitleCase:(C)C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_title_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_to_title_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toTitleCase:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_title_case_int(
  conversion_inputt &target)
{
  return convert_to_title_case_char(target);
}

/// Converts the character argument to uppercase.
///
///    TODO: For now we only consider ASCII characters but ultimately
///          we should use case mapping information from the
///          UnicodeData file
/// \param chr: An expression of type character
/// \param type: A type for the output
/// \return An expression of the given type
exprt character_refine_preprocesst::expr_of_to_upper_case(
  const exprt &chr, const typet &type)
{
  minus_exprt transformed(
    plus_exprt(chr, from_integer('A', type)), from_integer('a', type));

  if_exprt res(expr_of_is_ascii_lower_case(chr, type), transformed, chr);
  return std::move(res);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toUpperCase:(C)C
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_upper_case_char(
  conversion_inputt &target)
{
  return convert_char_function(
    &character_refine_preprocesst::expr_of_to_upper_case, target);
}

/// Converts function call to an assignment of an expression corresponding to
/// the java method Character.toUpperCase:(I)I
/// \param target: a position in a goto program
codet character_refine_preprocesst::convert_to_upper_case_int(
  conversion_inputt &target)
{
  return convert_to_upper_case_char(target);
}

/// replace function calls to functions of the Character by an affectation if
/// possible, returns the same code otherwise. For this method to have an effect
/// initialize_conversion_table must have been called before.
/// \param code: the code of a function call
/// \return code where character function call get replaced by an simple
///   instruction
codet character_refine_preprocesst::replace_character_call(
  const code_function_callt &code) const
{
  if(code.function().id()==ID_symbol)
  {
    const irep_idt &function_id=
      to_symbol_expr(code.function()).get_identifier();
    auto it=conversion_table.find(function_id);
    if(it!=conversion_table.end())
      return (it->second)(code);
  }

  return code;
}

/// fill maps with correspondance from java method names to conversion functions
void character_refine_preprocesst::initialize_conversion_table()
{
  // All methods are listed here in alphabetic order
  // The ones that are not supported by this module (though they may be
  // supported by the string solver) have no entry in the conversion
  // table and are marked in this way:
  // Not supported "java::java.lang.Character.<init>()"

  conversion_table["java::java.lang.Character.charCount:(I)I"]=
      &character_refine_preprocesst::convert_char_count;
  conversion_table["java::java.lang.Character.charValue:()C"]=
      &character_refine_preprocesst::convert_char_value;

  // Not supported "java::java.lang.Character.codePointAt:([CI)I
  // Not supported "java::java.lang.Character.codePointAt:([CII)I"
  // Not supported "java::java.lang.Character.codePointAt:"
  //   "(Ljava.lang.CharSequence;I)I"
  // Not supported "java::java.lang.Character.codePointBefore:([CI)I"
  // Not supported "java::java.lang.Character.codePointBefore:([CII)I"
  // Not supported "java::java.lang.Character.codePointBefore:"
  //   "(Ljava.lang.CharSequence;I)I"
  // Not supported "java::java.lang.Character.codePointCount:([CII)I"
  // Not supported "java::java.lang.Character.codePointCount:"
  //   "(Ljava.lang.CharSequence;II)I"
  // Not supported "java::java.lang.Character.compareTo:"
  //   "(Ljava.lang.Character;)I"

  conversion_table["java::java.lang.Character.compare:(CC)I"]=
      &character_refine_preprocesst::convert_compare;
  conversion_table["java::java.lang.Character.digit:(CI)I"]=
      &character_refine_preprocesst::convert_digit_char;
  conversion_table["java::java.lang.Character.digit:(II)I"]=
      &character_refine_preprocesst::convert_digit_int;

  // Not supported "java::java.lang.Character.equals:(Ljava.lang.Object;)Z"

  conversion_table["java::java.lang.Character.forDigit:(II)C"]=
      &character_refine_preprocesst::convert_for_digit;
  conversion_table["java::java.lang.Character.getDirectionality:(C)B"]=
      &character_refine_preprocesst::convert_get_directionality_char;
  conversion_table["java::java.lang.Character.getDirectionality:(I)B"]=
      &character_refine_preprocesst::convert_get_directionality_int;

  // Not supported "java::java.lang.Character.getName:(I)Ljava.lang.String;"

  conversion_table["java::java.lang.Character.getNumericValue:(C)I"]=
      &character_refine_preprocesst::convert_get_numeric_value_char;
  conversion_table["java::java.lang.Character.getNumericValue:(I)I"]=
      &character_refine_preprocesst::convert_get_numeric_value_int;
  conversion_table["java::java.lang.Character.getType:(C)I"]=
      &character_refine_preprocesst::convert_get_type_char;
  conversion_table["java::java.lang.Character.getType:(I)I"]=
      &character_refine_preprocesst::convert_get_type_int;
  conversion_table["java::java.lang.Character.hashCode:()I"]=
      &character_refine_preprocesst::convert_hash_code;
  conversion_table["java::java.lang.Character.highSurrogate:(I)C"]=
      &character_refine_preprocesst::convert_high_surrogate;
  conversion_table["java::java.lang.Character.isAlphabetic:(I)Z"]=
      &character_refine_preprocesst::convert_is_alphabetic;
  conversion_table["java::java.lang.Character.isBmpCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_bmp_code_point;
  conversion_table["java::java.lang.Character.isDefined:(C)Z"]=
      &character_refine_preprocesst::convert_is_defined_char;
  conversion_table["java::java.lang.Character.isDefined:(I)Z"]=
      &character_refine_preprocesst::convert_is_defined_int;
  conversion_table["java::java.lang.Character.isDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_digit_char;
  conversion_table["java::java.lang.Character.isDigit:(I)Z"]=
      &character_refine_preprocesst::convert_is_digit_int;
  conversion_table["java::java.lang.Character.isHighSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_high_surrogate;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(C)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_char;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(I)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_int;
  conversion_table["java::java.lang.Character.isIdeographic:(I)Z"]=
      &character_refine_preprocesst::convert_is_ideographic;
  conversion_table["java::java.lang.Character.isISOControl:(C)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_char;
  conversion_table["java::java.lang.Character.isISOControl:(I)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(I)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(I)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_int;
  conversion_table["java::java.lang.Character.isJavaLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter;
  conversion_table["java::java.lang.Character.isJavaLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter_or_digit;
  conversion_table["java::java.lang.Character.isLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_char;
  conversion_table["java::java.lang.Character.isLetter:(I)Z"]=
      &character_refine_preprocesst::convert_is_letter_int;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_char;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(I)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_int;
  conversion_table["java::java.lang.Character.isLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_char;
  conversion_table["java::java.lang.Character.isLowerCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_int;
  conversion_table["java::java.lang.Character.isLowSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_low_surrogate;
  conversion_table["java::java.lang.Character.isMirrored:(C)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_char;
  conversion_table["java::java.lang.Character.isMirrored:(I)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_int;
  conversion_table["java::java.lang.Character.isSpace:(C)Z"]=
      &character_refine_preprocesst::convert_is_space;
  conversion_table["java::java.lang.Character.isSpaceChar:(C)Z"]=
      &character_refine_preprocesst::convert_is_space_char;
  conversion_table["java::java.lang.Character.isSpaceChar:(I)Z"]=
      &character_refine_preprocesst::convert_is_space_char_int;
  conversion_table["java::java.lang.Character.isSupplementaryCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_supplementary_code_point;
  conversion_table["java::java.lang.Character.isSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_surrogate;
  conversion_table["java::java.lang.Character.isSurrogatePair:(CC)Z"]=
      &character_refine_preprocesst::convert_is_surrogate_pair;
  conversion_table["java::java.lang.Character.isTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_title_case_char;
  conversion_table["java::java.lang.Character.isTitleCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_title_case_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(I)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(I)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_int;
  conversion_table["java::java.lang.Character.isUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_char;
  conversion_table["java::java.lang.Character.isUpperCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_int;
  conversion_table["java::java.lang.Character.isValidCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_valid_code_point;
  conversion_table["java::java.lang.Character.isWhitespace:(C)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_char;
  conversion_table["java::java.lang.Character.isWhitespace:(I)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_int;
  conversion_table["java::java.lang.Character.lowSurrogate:(I)C"]=
      &character_refine_preprocesst::convert_is_low_surrogate;

  // Not supported "java::java.lang.Character.offsetByCodePoints:([CIIII)I"
  // Not supported "java::java.lang.Character.offsetByCodePoints:"
  //   "(Ljava.lang.CharacterSequence;II)I"

  conversion_table["java::java.lang.Character.reverseBytes:(C)C"]=
      &character_refine_preprocesst::convert_reverse_bytes;
  conversion_table["java::java.lang.Character.toChars:(I)[C"]=
      &character_refine_preprocesst::convert_to_chars;

  // Not supported "java::java.lang.Character.toChars:(I[CI)I"

  conversion_table["java::java.lang.Character.toCodePoint:(CC)I"]=
      &character_refine_preprocesst::convert_to_code_point;
  conversion_table["java::java.lang.Character.toLowerCase:(C)C"]=
      &character_refine_preprocesst::convert_to_lower_case_char;
  conversion_table["java::java.lang.Character.toLowerCase:(I)I"]=
      &character_refine_preprocesst::convert_to_lower_case_int;

  // Not supported "java::java.lang.Character.toString:()Ljava.lang.String;"
  // Not supported "java::java.lang.Character.toString:(C)Ljava.lang.String;"

  conversion_table["java::java.lang.Character.toTitleCase:(C)C"]=
      &character_refine_preprocesst::convert_to_title_case_char;
  conversion_table["java::java.lang.Character.toTitleCase:(I)I"]=
      &character_refine_preprocesst::convert_to_title_case_int;
  conversion_table["java::java.lang.Character.toUpperCase:(C)C"]=
      &character_refine_preprocesst::convert_to_upper_case_char;
  conversion_table["java::java.lang.Character.toUpperCase:(I)I"]=
      &character_refine_preprocesst::convert_to_upper_case_int;

  // Not supported "java::java.lang.Character.valueOf:(C)Ljava.lang.Character;"
}
