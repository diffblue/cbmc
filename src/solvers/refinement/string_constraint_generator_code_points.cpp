/*******************************************************************\

Module: Generates string constraints for Java functions dealing with
        code points

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for Java functions dealing with code points

#include <solvers/refinement/string_constraint_generator.h>

/// add axioms for the conversion of an integer representing a java
/// code point to a utf-16 string
/// \param fresh_symbol: generator of fresh symbols
/// \param res: array of characters corresponding to the result fo the function
/// \param code_point: an expression representing a java code point
/// \return integer expression equal to zero
std::pair<exprt, string_constraintst> add_axioms_for_code_point(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &code_point)
{
  string_constraintst constraints;
  const typet &char_type = res.content().type().subtype();
  const typet &type=code_point.type();
  PRECONDITION(type.id()==ID_signedbv);

  // We add axioms:
  // a1 : code_point<0x010000 => |res|=1
  // a2 : code_point>=0x010000 => |res|=2
  // a3 : code_point<0x010000 => res[0]=code_point
  // a4 : code_point>=0x010000 => res[0]=0xD800+(code_point-0x10000)/0x0400
  // a5 : code_point>=0x010000 => res[1]=0xDC00+(code_point-0x10000)/0x0400
  // For more explenations about this conversion, see:
  //   https://en.wikipedia.org/wiki/UTF-16

  exprt hex010000=from_integer(0x010000, type);
  exprt hexD800=from_integer(0xD800, type);
  exprt hexDC00=from_integer(0xDC00, type);
  exprt hex0400=from_integer(0x0400, type);

  binary_relation_exprt small(code_point, ID_lt, hex010000);
  implies_exprt a1(small, length_eq(res, 1));
  constraints.existential.push_back(a1);

  implies_exprt a2(not_exprt(small), length_eq(res, 2));
  constraints.existential.push_back(a2);

  typecast_exprt code_point_as_char(code_point, char_type);
  implies_exprt a3(small, equal_exprt(res[0], code_point_as_char));
  constraints.existential.push_back(a3);

  plus_exprt first_char(
    hexD800, div_exprt(minus_exprt(code_point, hex010000), hex0400));
  implies_exprt a4(
    not_exprt(small),
    equal_exprt(res[0], typecast_exprt(first_char, char_type)));
  constraints.existential.push_back(a4);

  plus_exprt second_char(hexDC00, mod_exprt(code_point, hex0400));
  implies_exprt a5(
    not_exprt(small),
    equal_exprt(res[1], typecast_exprt(second_char, char_type)));
  constraints.existential.push_back(a5);

  return {from_integer(0, get_return_code_type()), constraints};
}

/// the output is true when the character is a high surrogate for UTF-16
/// encoding, see https://en.wikipedia.org/wiki/UTF-16 for more explenation
/// about the encoding; this is true when the character is in the range
/// 0xD800..0xDBFF
/// \param chr: a character expression
/// \return a Boolean expression
static exprt is_high_surrogate(const exprt &chr)
{
  return and_exprt(
    binary_relation_exprt(chr, ID_ge, from_integer(0xD800, chr.type())),
    binary_relation_exprt(chr, ID_le, from_integer(0xDBFF, chr.type())));
}

/// the output is true when the character is a low surrogate for UTF-16
/// encoding, see https://en.wikipedia.org/wiki/UTF-16 for more explenation
/// about the encoding; this is true when the character is in the range
/// 0xDC00..0xDFFF
/// \param chr: a character expression
/// \return a Boolean expression
static exprt is_low_surrogate(const exprt &chr)
{
  return and_exprt(
    binary_relation_exprt(chr, ID_ge, from_integer(0xDC00, chr.type())),
    binary_relation_exprt(chr, ID_le, from_integer(0xDFFF, chr.type())));
}

/// the output corresponds to the unicode character given by the pair of
/// characters of inputs assuming it has been encoded in UTF-16, see
/// https://en.wikipedia.org/wiki/UTF-16 for more explenation about the
/// encoding; the operation we perform is:
/// pair_value=0x10000+(((char1%0x0800)*0x0400)+char2%0x0400)
/// \param char1: a character expression
/// \param char2: a character expression
/// \param return_type: type of the expression to return
/// \return an integer expression of type return_type
exprt pair_value(exprt char1, exprt char2, typet return_type)
{
  exprt hex010000=from_integer(0x010000, return_type);
  exprt hex0800=from_integer(0x0800, return_type);
  exprt hex0400=from_integer(0x0400, return_type);
  mult_exprt m1(mod_exprt(char1, hex0800), hex0400);
  mod_exprt m2(char2, hex0400);
  plus_exprt pair_value(hex010000, plus_exprt(m1, m2));
  return std::move(pair_value);
}

/// add axioms corresponding to the String.codePointAt java function
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments a string and an
///   index
/// \param array_pool: pool of arrays representing strings
/// \return a integer expression corresponding to a code point
std::pair<exprt, string_constraintst> add_axioms_for_code_point_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  string_constraintst constraints;
  const typet &return_type = f.type();
  PRECONDITION(return_type.id()==ID_signedbv);
  PRECONDITION(f.arguments().size() == 2);
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);
  const exprt &pos = f.arguments()[1];

  const symbol_exprt result = fresh_symbol("char", return_type);
  const exprt index1 = from_integer(1, str.length().type());
  const exprt &char1=str[pos];
  const exprt &char2 = str[plus_exprt(pos, index1)];
  const typecast_exprt char1_as_int(char1, return_type);
  const typecast_exprt char2_as_int(char2, return_type);
  const exprt pair = pair_value(char1_as_int, char2_as_int, return_type);
  const exprt is_low = is_low_surrogate(str[plus_exprt(pos, index1)]);
  const and_exprt return_pair(is_high_surrogate(str[pos]), is_low);

  constraints.existential.push_back(
    implies_exprt(return_pair, equal_exprt(result, pair)));
  constraints.existential.push_back(
    implies_exprt(not_exprt(return_pair), equal_exprt(result, char1_as_int)));
  return {result, constraints};
}

/// add axioms corresponding to the String.codePointBefore java function
/// \par parameters: function application with two arguments: a string and an
///   index
/// \return a integer expression corresponding to a code point
std::pair<exprt, string_constraintst> add_axioms_for_code_point_before(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size()==2);
  typet return_type=f.type();
  PRECONDITION(return_type.id()==ID_signedbv);
  symbol_exprt result=fresh_symbol("char", return_type);
  array_string_exprt str = get_string_expr(array_pool, args[0]);
  string_constraintst constraints;

  const exprt &char1=
    str[minus_exprt(args[1], from_integer(2, str.length().type()))];
  const exprt &char2=
    str[minus_exprt(args[1], from_integer(1, str.length().type()))];
  const typecast_exprt char1_as_int(char1, return_type);
  const typecast_exprt char2_as_int(char2, return_type);

  const exprt pair = pair_value(char1_as_int, char2_as_int, return_type);
  const and_exprt return_pair(
    is_high_surrogate(char1), is_low_surrogate(char2));

  constraints.existential.push_back(
    implies_exprt(return_pair, equal_exprt(result, pair)));
  constraints.existential.push_back(
    implies_exprt(not_exprt(return_pair), equal_exprt(result, char2_as_int)));
  return {result, constraints};
}

/// add axioms giving approximate bounds on the result of the
/// String.codePointCount java function
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments string `str`, integer
///           `begin` and integer `end`.
/// \param array_pool: pool of arrays representing strings
/// \return an integer expression
std::pair<exprt, string_constraintst> add_axioms_for_code_point_count(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 3);
  string_constraintst constraints;
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);
  const exprt &begin = f.arguments()[1];
  const exprt &end = f.arguments()[2];
  const typet &return_type=f.type();
  const symbol_exprt result = fresh_symbol("code_point_count", return_type);
  const minus_exprt length(end, begin);
  const div_exprt minimum(length, from_integer(2, length.type()));
  constraints.existential.push_back(
    binary_relation_exprt(result, ID_le, length));
  constraints.existential.push_back(
    binary_relation_exprt(result, ID_ge, minimum));

  return {result, constraints};
}

/// add axioms giving approximate bounds on the result of the
/// String.offsetByCodePointCount java function. We approximate the result by
/// saying the result is between index + offset and index + 2 * offset
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments string `str`, integer `index`
///           and integer `offset`.
/// \return a new string expression
std::pair<exprt, string_constraintst> add_axioms_for_offset_by_code_point(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  string_constraintst constraints;
  const exprt &index = f.arguments()[1];
  const exprt &offset = f.arguments()[2];
  const typet &return_type=f.type();
  const symbol_exprt result = fresh_symbol("offset_by_code_point", return_type);

  const exprt minimum = plus_exprt(index, offset);
  const exprt maximum = plus_exprt(minimum, offset);
  constraints.existential.push_back(
    binary_relation_exprt(result, ID_le, maximum));
  constraints.existential.push_back(
    binary_relation_exprt(result, ID_ge, minimum));

  return {result, constraints};
}

