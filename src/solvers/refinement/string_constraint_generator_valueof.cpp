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

const exprt get_radix_from_optional_second_argument(
  const function_application_exprt &f, const typet &type)
{
  return f.arguments().size()==1?
    static_cast<exprt>(from_integer(10, type)):
    static_cast<exprt>(typecast_exprt(f.arguments()[1], type));
}

/// Add axioms corresponding to the String.valueOf(I) java function.
/// \param expr: function application with one integer argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  PRECONDITION(expr.arguments().size()>=1);
  const exprt &x=expr.arguments()[0];
  const exprt radix=get_radix_from_optional_second_argument(expr, x.type());
  return add_axioms_from_int(x, radix, ref_type);
}

/// Add axioms corresponding to the String.valueOf(J) java function.
/// \param expr: function application with one long argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_long(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  PRECONDITION(expr.arguments().size()>=1);
  const exprt &x=expr.arguments()[0];
  const exprt radix=get_radix_from_optional_second_argument(expr, x.type());
  return add_axioms_from_int(x, radix, ref_type);
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
  axioms.push_back(a1);

  for(std::size_t i=0; i<str_true.length(); i++)
  {
    exprt chr=from_integer(str_true[i], char_type);
    implies_exprt a2(eq, equal_exprt(res[i], chr));
    axioms.push_back(a2);
  }

  std::string str_false="false";
  implies_exprt a3(not_exprt(eq), res.axiom_for_has_length(str_false.length()));
  axioms.push_back(a3);

  for(std::size_t i=0; i<str_false.length(); i++)
  {
    exprt chr=from_integer(str_false[i], char_type);
    implies_exprt a4(not_exprt(eq), equal_exprt(res[i], chr));
    axioms.push_back(a4);
  }

  return res;
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(I) or String.valueOf(J) Java functions applied
/// on the integer expression.
/// \param x: a signed integer expression
/// \param max_size: a maximal size for the string representation
/// \param radix: an expression for the radix
/// \param ref_type: type for refined strings
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const exprt &x,
  const exprt radix,
  const refined_string_typet &ref_type)
{
  /// If we cannot tell what the radix is then so we assume it is 2 to make sure
  /// max_size will definitely be large enough
  double radix_d=static_cast<double>(try_to_evaluate_expr_as_ul(radix, 2ul));
  size_t max_size=calculate_max_string_length(x.type(), radix_d);

  return add_axioms_from_int(x, radix, ref_type, max_size);
}

/// Add axioms enforcing that the string corresponds to the result
/// of String.valueOf(I) or String.valueOf(J) Java functions applied
/// on the integer expression.
/// \param x: a signed integer expression
/// \param max_size: a maximal size for the string representation
/// \param ref_type: type for refined strings
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const exprt &x,
  const exprt radix,
  const refined_string_typet &ref_type,
  size_t max_size)
{
  PRECONDITION(x.type().id()==ID_signedbv);
  PRECONDITION(max_size<std::numeric_limits<size_t>::max());
  string_exprt res=fresh_string(ref_type);
  const typet &type=x.type();
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  exprt zero_char=constant_char('0', char_type);
  exprt radix_char_type=typecast_exprt(radix, char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt max=from_integer(max_size, index_type);
  unsigned long radix_ul=try_to_evaluate_expr_as_ul(radix, 36ul);

  // We add axioms:
  // a1 : x < 0 => 1 <|res|<=max_size && res[0]='-'
  // a2 : x >= 0 => 0 <|res|<=max_size-1 && res[0] is a digit for the radix
  // a3 : |res|>1 && res[0] is a digit for the radix => res[0]!='0'
  // a4 : |res|>1 && res[0]='-' => res[1]!='0'

  binary_relation_exprt is_negative(x, ID_lt, from_integer(0, type));
  and_exprt correct_length1(
    res.axiom_for_is_strictly_longer_than(1),
    res.axiom_for_is_shorter_than(max));
  equal_exprt starts_with_minus(res[0], minus_char);
  implies_exprt a1(is_negative, and_exprt(correct_length1, starts_with_minus));
  axioms.push_back(a1);

  not_exprt is_positive(is_negative);
  exprt starts_with_digit=
    is_digit_with_radix_lower_case(res[0], radix_char_type, radix_ul);
  and_exprt correct_length2(
    res.axiom_for_is_strictly_longer_than(0),
    res.axiom_for_is_strictly_shorter_than(max));
  implies_exprt a2(is_positive, and_exprt(correct_length2, starts_with_digit));
  axioms.push_back(a2);

  implies_exprt a3(
    and_exprt(res.axiom_for_is_strictly_longer_than(1), starts_with_digit),
    not_exprt(equal_exprt(res[0], zero_char)));
  axioms.push_back(a3);

  implies_exprt a4(
    and_exprt(res.axiom_for_is_strictly_longer_than(1), starts_with_minus),
    not_exprt(equal_exprt(res[1], zero_char)));
  axioms.push_back(a4);

  for(size_t size=1; size<=max_size; size++)
  {
    // For each possible size, we have:
    // sum_0 = numeric value of res[0] (which is 0 if res[0] is '-')
    // sum_j = radix * sum_{j-1} + numeric value of res[j]
    // and add axioms:
    // a5 : |res| == size =>
    //        forall 1 <= j < size.
    //          is_number && (j >= max_size-2 => no_overflow)
    //     where is_number := res[j] is a digit for the radix
    //     and no_overflow := sum_{j-1} = (radix * sum_{j-1} / radix)
    //                        && sum_j >= sum_{j - 1}
    //         (the first part avoid overflows in multiplication and
    //          the second one in additions)
    // a6 : |res| == size && res[0] is a digit for radix => x == sum
    // a7 : |res| == size && res[0] == '-' => x == -sum

    exprt::operandst digit_constraints;
    exprt sum=
      get_numeric_value_from_character(res[0], char_type, type, radix_ul);

    for(size_t j=1; j<size; j++)
    {
      mult_exprt radix_sum(sum, radix);
      // new_sum = radix * sum + (numeric value of res[j])
      exprt new_sum=plus_exprt(
        radix_sum,
        get_numeric_value_from_character(res[j], char_type, type, radix_ul));
      exprt is_number=
        is_digit_with_radix_lower_case(res[j], radix_char_type, radix_ul);
      digit_constraints.push_back(is_number);

      // An overflow can happen when reaching the last index of a string of
      // maximal size which is `max_size-1` for negative numbers and
      // `max_size - 2` for positive numbers because of the absence of a `-`
      // sign.
      if(j>=max_size-2)
      {
        and_exprt no_overflow(
          equal_exprt(sum, div_exprt(radix_sum, radix)),
          binary_relation_exprt(new_sum, ID_ge, radix_sum));
        digit_constraints.push_back(no_overflow);
      }
      sum=new_sum;
    }

    equal_exprt premise=res.axiom_for_has_length(size);
    implies_exprt a5(premise, conjunction(digit_constraints));
    axioms.push_back(a5);

    implies_exprt a6(
      and_exprt(premise, starts_with_digit), equal_exprt(x, sum));
    axioms.push_back(a6);

    implies_exprt a7(
      and_exprt(premise, starts_with_minus),
      equal_exprt(x, unary_minus_exprt(sum)));
    axioms.push_back(a7);
  }

  return res;
}

/// Returns the integer value represented by the character.
/// \param chr: a character expression in the following set:
///   0123456789abcdef
/// \return an integer expression
exprt string_constraint_generatort::int_of_hex_char(const exprt &chr) const
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
  axioms.push_back(
    and_exprt(res.axiom_for_is_strictly_longer_than(0),
              res.axiom_for_is_shorter_than(max_size)));

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
    axioms.push_back(
      implies_exprt(premise, and_exprt(equal_exprt(i, sum), all_numbers)));

    // disallow 0s at the beggining
    if(size>1)
      axioms.push_back(
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
  axioms.push_back(lemma);
  return res;
}

/// Add axioms corresponding to the String.valueOf([C) and String.valueOf([CII)
/// functions.
/// \param f: function application with one or three arguments
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_value_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  if(args.size()==3)
  {
    const refined_string_typet &ref_type=to_refined_string_type(f.type());
    string_exprt res=fresh_string(ref_type);
    exprt char_array=args[0];
    exprt offset=args[1];
    exprt count=args[2];

    // We add axioms:
    // a1 : |res| = count
    // a2 : forall idx<count, str[idx+offset]=res[idx]

    string_exprt str=add_axioms_for_java_char_array(char_array);
    axioms.push_back(res.axiom_for_has_length(count));

    symbol_exprt idx=fresh_univ_index(
      "QA_index_value_of", ref_type.get_index_type());
    equal_exprt eq(str[plus_exprt(idx, offset)], res[idx]);
    string_constraintt a2(idx, count, eq);
    axioms.push_back(a2);
    return res;
  }
  else
  {
    INVARIANT(
      args.size()==1,
      string_refinement_invariantt("f can only have 1 or 3 arguments and the "
        "case of 3 has been handled"));
    return add_axioms_for_java_char_array(args[0]);
  }
}

/// Add axioms making the return value true if the given string is a correct
/// number in the given radix
/// \param str: string expression
/// \param radix: the radix
/// \param max_size: maximum number of characters
void string_constraint_generatort::add_axioms_for_correct_number_format(
  const string_exprt &str, const exprt &radix_char_type, std::size_t max_size)
{
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt plus_char=constant_char('+', char_type);

  exprt chr=str[0];
  equal_exprt starts_with_minus(chr, minus_char);
  equal_exprt starts_with_plus(chr, plus_char);
  exprt starts_with_digit=is_digit_with_radix(chr, radix_char_type);

  // TODO: we should have implications in the other direction for correct
  // correct => |str| > 0
  exprt non_empty=str.axiom_for_is_longer_than(from_integer(1, index_type));
  axioms.push_back(non_empty);

  // correct => (str[0] = '+' or '-' || is_digit_with_radix(str[0], radix))
  or_exprt correct_first(
    or_exprt(starts_with_minus, starts_with_plus), starts_with_digit);
  axioms.push_back(correct_first);

  // correct => str[0]='+' or '-' ==> |str| > 1
  implies_exprt contains_digit(
    or_exprt(starts_with_minus, starts_with_plus),
    str.axiom_for_is_longer_than(from_integer(2, index_type)));
  axioms.push_back(contains_digit);

  // correct => |str| < max_size
  axioms.push_back(str.axiom_for_is_shorter_than(max_size));

  // forall 1 <= i < |str| . correct => is_digit_with_radix(str[i], radix)
  // We unfold the above because we know that it will be used for all i up to
  // str.length()
  for(std::size_t index=1; index<max_size; ++index)
  {
    const exprt index_expr=from_integer(index, index_type);
    /// index < length && correct => is_digit(str[index])
    implies_exprt character_at_index_is_digit(
      binary_relation_exprt(index_expr, ID_lt, str.length()),
      is_digit_with_radix(str[index], radix_char_type));
    axioms.push_back(character_at_index_is_digit);
  }
}

/// Add axioms connecting the characters in the input string to the value of the
/// output integer
/// \param x: symbol for abs(integer represented by str)
/// \param type: the type for x
/// \param char_type: the type to use for characters
/// \param index_type: the type to use for indexes
/// \param str: input string
/// \param max_string_length: the maximum length str can have
/// \param radix: the radix, with the same type as x
/// \return an expression for the integer represented by the string
exprt string_constraint_generatort::add_axioms_for_characters_in_integer_string(
  const symbol_exprt& x,
  const typet& type,
  const typet& char_type,
  const typet& index_type,
  const string_exprt& str,
  const std::size_t max_string_length,
  const exprt& radix)
{
  /// TODO(OJones): Fix the below algorithm to make it work for min_int. There
  /// are two problems. (1) Because we build i as positive and then negate it if
  /// the first character is '-', we hit overflow for min_int because
  /// |min_int| > max_int. (2) radix^63 overflows. I think we'll have to
  /// special-case it.

  const exprt zero_expr=from_integer(0, type);
  axioms.push_back(binary_relation_exprt(x, ID_ge, zero_expr));

  const exprt one_index_type=from_integer(1, index_type);
  exprt radix_to_power_of_i;
  exprt no_overflow;

  for(std::size_t i=0; i<max_string_length; ++i)
  {
    /// We are counting backwards from the end of the string, i.e. i refers
    /// to str[j] where j=str.length()-i-1
    const constant_exprt i_expr=from_integer(i, index_type);
    const minus_exprt j(minus_exprt(str.length(), i_expr), one_index_type);

    if(i==0)
    {
      no_overflow=true_exprt();
      radix_to_power_of_i=from_integer(1, type);
    }
    else
    {
      const exprt radix_to_power_of_i_minus_one=radix_to_power_of_i;
      /// Note that power_exprt is probably designed for floating point. Also,
      /// it doesn't work when the exponent isn't a constant, hence why this
      /// loop is indexed by i instead of j. It is faster than
      /// mult_exprt(radix_to_power_of_i, radix).
      radix_to_power_of_i=power_exprt(radix, i_expr);
      /// The first time there is overflow we will have that
      /// radix^i/radix != radix^(i-1)
      /// However, that condition may hold in future, so we have to be sure to
      /// propagate the first time this fails to all higher values of i
      no_overflow=and_exprt(
        equal_exprt(
          div_exprt(radix_to_power_of_i, radix), radix_to_power_of_i_minus_one),
        no_overflow);
    }

    /// If we have already read all characters from the string then we use 0
    /// instead of the value from str[j]
    const binary_relation_exprt i_is_valid(i_expr, ID_lt, str.length());
    const if_exprt digit_value(
      i_is_valid,
      get_numeric_value_from_character(str[j], char_type, type),
      zero_expr);

    /// when there is no overflow, str[j] = (x/radix^i)%radix
    const equal_exprt contribution_of_str_j(
      digit_value,
      mod_exprt(div_exprt(x, radix_to_power_of_i), radix));

    axioms.push_back(implies_exprt(no_overflow, contribution_of_str_j));
    axioms.push_back(implies_exprt(
      not_exprt(no_overflow), equal_exprt(digit_value, zero_expr)));
  }

  return if_exprt(
    equal_exprt(str[0], constant_char('-', char_type)),
    unary_minus_exprt(x),
    x);
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
  const exprt radix=get_radix_from_optional_second_argument(f, type);

  const symbol_exprt x=fresh_symbol("abs_parsed_int", type);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();

  /// We experimented with making the max_string_length depend on the base, but
  /// this did not make any difference to the speed of execution.
  const std::size_t max_string_length=to_bitvector_type(type).get_width()+1;

  /// TODO: we should throw an exception when this does not hold:
  /// Note that the only thing stopping us from taking longer strings with many
  /// leading zeros is the axioms for correct number format
  add_axioms_for_correct_number_format(
    str, typecast_exprt(radix, char_type), max_string_length);

  exprt parsed_int_expr=add_axioms_for_characters_in_integer_string(
    x, type, char_type, index_type, str, max_string_length, radix);

  return parsed_int_expr;
}

/// Check if a character is a digit with respect to the given radix, e.g. if the
/// radix is 10 then check if the character is in the range 0-9.
/// \param chr: the character
/// \param radix:  the radix
/// \return an expression for the condition
exprt is_digit_with_radix(const exprt &chr, const exprt &radix_char_type)
{
  const typet &char_type=chr.type();
  const exprt zero_char=from_integer('0', char_type);
  const exprt nine_char=from_integer('9', char_type);
  const exprt a_char=from_integer('a', char_type);
  const exprt A_char=from_integer('A', char_type);
  const constant_exprt ten_char_type=from_integer(10, char_type);

  const and_exprt is_digit_when_radix_le_10(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(
      chr, ID_lt, plus_exprt(zero_char, radix_char_type)));

  const minus_exprt radix_minus_ten(radix_char_type, ten_char_type);

  const or_exprt is_digit_when_radix_gt_10(
    and_exprt(
      binary_relation_exprt(chr, ID_ge, zero_char),
      binary_relation_exprt(chr, ID_le, nine_char)),
    and_exprt(
      binary_relation_exprt(chr, ID_ge, a_char),
      binary_relation_exprt(chr, ID_lt, plus_exprt(a_char, radix_minus_ten))),
    and_exprt(
      binary_relation_exprt(chr, ID_ge, A_char),
      binary_relation_exprt(chr, ID_lt, plus_exprt(A_char, radix_minus_ten))));

  return if_exprt(
    binary_relation_exprt(radix_char_type, ID_le, ten_char_type),
    is_digit_when_radix_le_10,
    is_digit_when_radix_gt_10);
}

/// Check if a character is a digit with respect to the given radix, e.g. if the
/// radix is 10 then check if the character is in the range 0-9. For bases above
/// 10 only lower case letters are allowed, not upper case.
/// \param chr: the character
/// \param radix_char_type:  the radix as an expression of the same type as chr
/// \param radix: the radix, which should be between 2 and 36 (default 36)
/// \return an expression for the condition
exprt is_digit_with_radix_lower_case(
  const exprt &chr, const exprt &radix_char_type, unsigned long radix)
{
  const typet &char_type=chr.type();
  const exprt zero_char=from_integer('0', char_type);
  const exprt nine_char=from_integer('9', char_type);
  const exprt a_char=from_integer('a', char_type);
  const constant_exprt ten_char_type=from_integer(10, char_type);

  const and_exprt is_digit_when_radix_le_10(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(chr, ID_lt, plus_exprt(zero_char, radix_char_type)));

  if(radix<=10)
  {
    return is_digit_when_radix_le_10;
  }
  else
  {
    const minus_exprt radix_minus_ten(radix_char_type, ten_char_type);

    const or_exprt is_digit_when_radix_gt_10(
      and_exprt(
        binary_relation_exprt(chr, ID_ge, zero_char),
        binary_relation_exprt(chr, ID_le, nine_char)),
        and_exprt(
          binary_relation_exprt(chr, ID_ge, a_char),
          binary_relation_exprt(chr, ID_lt, plus_exprt(a_char, radix_minus_ten))));

    return if_exprt(
      binary_relation_exprt(radix_char_type, ID_le, ten_char_type),
      is_digit_when_radix_le_10,
      is_digit_when_radix_gt_10);
  }
}

/// Get the numeric value of a character, assuming that the radix is large
/// enough. '+' and '-' yield 0.
/// \param chr: the character to get the numeric value of
/// \param char_type: the type to use for characters
/// \param type: the type to use for the return value
/// \param radix: the radix, which should be between 2 and 36 (default 36)
/// \return an integer expression of the given type with the numeric value of
///   the char
exprt get_numeric_value_from_character(
  const exprt &chr,
  const typet &char_type,
  const typet &type,
  unsigned long radix)
{
  const constant_exprt zero_char=from_integer('0', char_type);
  const constant_exprt ten_int=from_integer(10, char_type);
  const constant_exprt a_char=from_integer('a', char_type);
  const constant_exprt A_char=from_integer('A', char_type);

  /// There are four cases, which occur in ASCII in the following order:
  /// '+' and '-', digits, upper case letters, lower case letters
  const binary_relation_exprt upper_case_lower_case_or_digit(
    chr, ID_ge, zero_char);

  if(radix<=10)
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
    const binary_relation_exprt lower_case(chr, ID_ge, a_char);
    const binary_relation_exprt upper_case_or_lower_case(chr, ID_ge, A_char);
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

/// Calculate the string length needed to represent any value of the given type
/// using the given radix
/// \param type: the type that we are considering values of
/// \param radix: the radix we are using, as a double
/// \return the maximum string length
size_t calculate_max_string_length(const typet &type, double radix)
{
  double n_bits=static_cast<double>(to_bitvector_type(type).get_width());

  /// If the type is signed then the maximum absolute value that needs to be
  /// representable is one bit smaller
  bool signed_type=type.id()==ID_signedbv;
  /// Let m be the minimal number of characters needed.
  /// For signed types, the longest string will be for -2^(n-1), so
  ///   m = 1 + min{k: 2^(n-1) < r^k}
  ///     = 1 + min{k: n-1 < k log_2(r)}
  ///     = 1 + min{k: k > (n-1) / log_2(r)}
  ///     = 1 + min{k: k > floor((n-1) / log_2(r))}
  ///     = 1 + (1 + floor((n-1) / log_2(r)))
  ///     = 2 + floor((n-1) / log_2(r))
  /// For unsigned types, the longest string will be for (2^n)-1, so
  ///   m = min{k: (2^n)-1 < r^k}
  ///     = min{k: 2^n <= r^k}
  ///     = min{k: n <= k log_2(r)}
  ///     = min{k: k >= n / log_2(r)}
  ///     = min{k: k >= ceil(n / log_2(r))}
  ///     = ceil(n / log_2(r))
  double max_string_length=signed_type?
    floor(static_cast<double>(n_bits-1)/log2(radix))+2.0:
    ceil(static_cast<double>(n_bits)/log2(radix));
  return static_cast<size_t>(max_string_length);
}

/// If the expression is a constant expression then we get the value of it as
/// an unsigned long. If not we return a default value.
/// \param expr: input expression
/// \param def: default value to return if we cannot evaluate expr
/// \return the output as an unsigned long
unsigned long try_to_evaluate_expr_as_ul(const exprt &expr, unsigned long def)
{
  symbol_tablet symtab;
  const namespacet ns(symtab);
  mp_integer mp_radix;
  bool to_integer_failed=to_integer(simplify_expr(expr, ns), mp_radix);
  return to_integer_failed?def:integer2ulong(mp_radix);
}
