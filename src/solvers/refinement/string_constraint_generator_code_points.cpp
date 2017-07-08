/*******************************************************************\

Module: Generates string constraints for Java functions dealing with
        code points

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for Java functions dealing with code points

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************    \

Function: string_constraint_generatort::add_axioms_for_code_point

  Inputs: an expression representing a java code point

 Outputs: a new string expression

 Purpose: add axioms for the conversion of an integer representing a java
          code point to a utf-16 string

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_code_point(
  const exprt &code_point, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &type=code_point.type();
  assert(type.id()==ID_signedbv);

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
  implies_exprt a1(small, res.axiom_for_has_length(1));
  axioms.push_back(a1);

  implies_exprt a2(not_exprt(small), res.axiom_for_has_length(2));
  axioms.push_back(a2);

  typecast_exprt code_point_as_char(code_point, ref_type.get_char_type());
  implies_exprt a3(small, equal_exprt(res[0], code_point_as_char));
  axioms.push_back(a3);

  plus_exprt first_char(
    hexD800, div_exprt(minus_exprt(code_point, hex010000), hex0400));
  implies_exprt a4(
    not_exprt(small),
    equal_exprt(res[0], typecast_exprt(first_char, ref_type.get_char_type())));
  axioms.push_back(a4);

  plus_exprt second_char(hexDC00, mod_exprt(code_point, hex0400));
  implies_exprt a5(
    not_exprt(small),
    equal_exprt(res[1], typecast_exprt(second_char, ref_type.get_char_type())));
  axioms.push_back(a5);

  return res;
}

/// the output is true when the character is a high surrogate for UTF-16
/// encoding, see https://en.wikipedia.org/wiki/UTF-16 for more explenation
/// about the encoding; this is true when the character is in the range
/// 0xD800..0xDBFF
/// \par parameters: a character expression
/// \return a Boolean expression
exprt string_constraint_generatort::is_high_surrogate(const exprt &chr) const
{
  return and_exprt(
    binary_relation_exprt(chr, ID_ge, constant_char(0xD800, chr.type())),
    binary_relation_exprt(chr, ID_le, constant_char(0xDBFF, chr.type())));
}

/// the output is true when the character is a low surrogate for UTF-16
/// encoding, see https://en.wikipedia.org/wiki/UTF-16 for more explenation
/// about the encoding; this is true when the character is in the range
/// 0xDC00..0xDFFF
/// \par parameters: a character expression
/// \return a Boolean expression
exprt string_constraint_generatort::is_low_surrogate(const exprt &chr) const
{
  return and_exprt(
    binary_relation_exprt(chr, ID_ge, constant_char(0xDC00, chr.type())),
    binary_relation_exprt(chr, ID_le, constant_char(0xDFFF, chr.type())));
}

/// the output corresponds to the unicode character given by the pair of
/// characters of inputs assuming it has been encoded in UTF-16, see
/// https://en.wikipedia.org/wiki/UTF-16 for more explenation about the
/// encoding; the operation we perform is:
/// pair_value=0x10000+(((char1%0x0800)*0x0400)+char2%0x0400)
/// \par parameters: two character expressions and a return type
/// char1 and char2 should be of type return_type
/// \return an integer expression of type return_type
exprt pair_value(exprt char1, exprt char2, typet return_type)
{
  exprt hex010000=from_integer(0x010000, return_type);
  exprt hex0800=from_integer(0x0800, return_type);
  exprt hex0400=from_integer(0x0400, return_type);
  mult_exprt m1(mod_exprt(char1, hex0800), hex0400);
  mod_exprt m2(char2, hex0400);
  plus_exprt pair_value(hex010000, plus_exprt(m1, m2));
  return pair_value;
}

/// add axioms corresponding to the String.codePointAt java function
/// \par parameters: function application with two arguments: a string and an
///   index
/// \return a integer expression corresponding to a code point
exprt string_constraint_generatort::add_axioms_for_code_point_at(
  const function_application_exprt &f)
{
  typet return_type=f.type();
  assert(return_type.id()==ID_signedbv);
  string_exprt str=get_string_expr(args(f, 2)[0]);
  const exprt &pos=args(f, 2)[1];

  symbol_exprt result=fresh_symbol("char", return_type);
  exprt index1=from_integer(1, str.length().type());
  const exprt &char1=str[pos];
  const exprt &char2=str[plus_exprt_with_overflow_check(pos, index1)];
  exprt char1_as_int=typecast_exprt(char1, return_type);
  exprt char2_as_int=typecast_exprt(char2, return_type);
  exprt pair=pair_value(char1_as_int, char2_as_int, return_type);
  exprt is_low=is_low_surrogate(
    str[plus_exprt_with_overflow_check(pos, index1)]);
  exprt return_pair=and_exprt(is_high_surrogate(str[pos]), is_low);

  axioms.push_back(implies_exprt(return_pair, equal_exprt(result, pair)));
  axioms.push_back(
    implies_exprt(not_exprt(return_pair), equal_exprt(result, char1_as_int)));
  return result;
}

/// add axioms corresponding to the String.codePointBefore java function
/// \par parameters: function application with two arguments: a string and an
///   index
/// \return a integer expression corresponding to a code point
exprt string_constraint_generatort::add_axioms_for_code_point_before(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2);
  typet return_type=f.type();
  assert(return_type.id()==ID_signedbv);
  symbol_exprt result=fresh_symbol("char", return_type);
  string_exprt str=get_string_expr(args[0]);

  const exprt &char1=
    str[minus_exprt(args[1], from_integer(2, str.length().type()))];
  const exprt &char2=
    str[minus_exprt(args[1], from_integer(1, str.length().type()))];
  exprt char1_as_int=typecast_exprt(char1, return_type);
  exprt char2_as_int=typecast_exprt(char2, return_type);

  exprt pair=pair_value(char1_as_int, char2_as_int, return_type);
  exprt return_pair=and_exprt(
    is_high_surrogate(char1), is_low_surrogate(char2));

  axioms.push_back(implies_exprt(return_pair, equal_exprt(result, pair)));
  axioms.push_back(
    implies_exprt(not_exprt(return_pair), equal_exprt(result, char2_as_int)));
  return result;
}

/// add axioms giving approximate bounds on the result of the
/// String.codePointCount java function
/// \par parameters: function application with three arguments: a string and two
///   indexes
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_code_point_count(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 3)[0]);
  const exprt &begin=args(f, 3)[1];
  const exprt &end=args(f, 3)[2];
  const typet &return_type=f.type();
  symbol_exprt result=fresh_symbol("code_point_count", return_type);
  minus_exprt length(end, begin);
  div_exprt minimum(length, from_integer(2, length.type()));
  axioms.push_back(binary_relation_exprt(result, ID_le, length));
  axioms.push_back(binary_relation_exprt(result, ID_ge, minimum));

  return result;
}

/// add axioms giving approximate bounds on the result of the
/// String.offsetByCodePointCount java function. We approximate the result by
/// saying the result is between index + offset and index + 2 * offset
/// \par parameters: function application with three arguments: a string and two
///   indexes
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_offset_by_code_point(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 3)[0]);
  const exprt &index=args(f, 3)[1];
  const exprt &offset=args(f, 3)[2];
  const typet &return_type=f.type();
  symbol_exprt result=fresh_symbol("offset_by_code_point", return_type);

  exprt minimum=plus_exprt_with_overflow_check(index, offset);
  exprt maximum=plus_exprt_with_overflow_check(
    index, plus_exprt_with_overflow_check(offset, offset));
  axioms.push_back(binary_relation_exprt(result, ID_le, maximum));
  axioms.push_back(binary_relation_exprt(result, ID_ge, minimum));

  return result;
}

