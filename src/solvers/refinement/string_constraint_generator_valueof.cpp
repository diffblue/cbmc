/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions generating strings from other
///   types, in particular int, long, float, double, char, bool

#include <solvers/refinement/string_constraint_generator.h>

/// Add axioms corresponding to the String.valueOf(I) java function.
/// \param expr: function application with one integer argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  return add_axioms_from_int(args(expr, 1)[0], MAX_INTEGER_LENGTH, ref_type);
}

/// Add axioms corresponding to the String.valueOf(J) java function.
/// \param expr: function application with one long argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_long(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  return add_axioms_from_int(args(expr, 1)[0], MAX_LONG_LENGTH, ref_type);
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

  assert(b.type()==bool_typet() || b.type().id()==ID_c_bool);

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
/// \param i: a signed integer expression
/// \param max_size: a maximal size for the string representation
/// \param ref_type: type for refined strings
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_from_int(
  const exprt &i, size_t max_size, const refined_string_typet &ref_type)
{
  PRECONDITION(i.type().id()==ID_signedbv);
  PRECONDITION(max_size<std::numeric_limits<size_t>::max());
  string_exprt res=fresh_string(ref_type);
  const typet &type=i.type();
  exprt ten=from_integer(10, type);
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt zero=from_integer(0, index_type);
  exprt max=from_integer(max_size, index_type);

  // We add axioms:
  // a1 : i < 0 => 1 <|res|<=max_size && res[0]='-'
  // a2 : i >= 0 => 0 <|res|<=max_size-1 && '0'<=res[0]<='9'
  // a3 : |res|>1 && '0'<=res[0]<='9' => res[0]!='0'
  // a4 : |res|>1 && res[0]='-' => res[1]!='0'

  binary_relation_exprt is_negative(i, ID_lt, zero);
  and_exprt correct_length1(
    res.axiom_for_is_strictly_longer_than(1),
    res.axiom_for_is_shorter_than(max));
  equal_exprt starts_with_minus(res[0], minus_char);
  implies_exprt a1(is_negative, and_exprt(correct_length1, starts_with_minus));
  axioms.push_back(a1);

  not_exprt is_positive(is_negative);
  and_exprt starts_with_digit(
    binary_relation_exprt(res[0], ID_ge, zero_char),
    binary_relation_exprt(res[0], ID_le, nine_char));
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
    // sum_0 = starts_with_digit ? res[0]-'0' : 0
    // sum_j = 10 * sum_{j-1} + res[i] - '0'
    // and add axioms:
    // a5 : |res| == size =>
    //        forall 1 <= j < size.
    //          is_number && (j >= max_size-2 => no_overflow)
    //     where is_number := '0' <= res[j] <= '9'
    //     and no_overflow := sum_{j-1} = (10 * sum_{j-1} / 10)
    //                        && sum_j >= sum_{j - 1}
    //         (the first part avoid overflows in multiplication and
    //          the second one in additions)
    // a6 : |res| == size && '0' <= res[0] <= '9' => i == sum
    // a7 : |res| == size && res[0] == '-' => i == -sum

    exprt::operandst digit_constraints;
    exprt sum=if_exprt(
      starts_with_digit,
      typecast_exprt(minus_exprt(res[0], zero_char), type),
      from_integer(0, type));

    for(size_t j=1; j<size; j++)
    {
      mult_exprt ten_sum(sum, ten);
      // sum = 10 * sum + (res[j] - '0')
      exprt new_sum=plus_exprt(
        ten_sum, typecast_exprt(minus_exprt(res[j], zero_char), type));
      and_exprt is_number(
        binary_relation_exprt(res[j], ID_ge, zero_char),
        binary_relation_exprt(res[j], ID_le, nine_char));
      digit_constraints.push_back(is_number);

      // An overflow can happen when reaching the last index of a string of
      // maximal size which is `max_size` for negative numbers and
      // `max_size - 1` for positive numbers because of the abscence of a `-`
      // sign.
      if(j>=max_size-2)
      {
        // check for overflows if the size is big
        and_exprt no_overflow(
          equal_exprt(sum, div_exprt(ten_sum, ten)),
          binary_relation_exprt(new_sum, ID_ge, ten_sum));
        digit_constraints.push_back(no_overflow);
      }
      sum=new_sum;
    }

    equal_exprt premise=res.axiom_for_has_length(size);
    implies_exprt a5(premise, conjunction(digit_constraints));
    axioms.push_back(a5);

    implies_exprt a6(
      and_exprt(premise, starts_with_digit), equal_exprt(i, sum));
    axioms.push_back(a6);

    implies_exprt a7(
      and_exprt(premise, starts_with_minus),
      equal_exprt(i, unary_minus_exprt(sum)));
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
  assert(type.id()==ID_signedbv);
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
    assert(args.size()==1);
    return add_axioms_for_java_char_array(args[0]);
  }
}

/// Add axioms making the return value true if the given string is a correct
/// number.
/// \param f: function application with one string expression
/// \return an boolean expression
exprt string_constraint_generatort::add_axioms_for_correct_number_format(
  const string_exprt &str, std::size_t max_size)
{
  symbol_exprt correct=fresh_boolean("correct_number_format");
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
  and_exprt starts_with_digit(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(chr, ID_le, nine_char));

  // TODO: we should have implications in the other direction for correct
  // correct => |str| > 0
  exprt non_empty=str.axiom_for_is_longer_than(from_integer(1, index_type));
  axioms.push_back(implies_exprt(correct, non_empty));

  // correct => (str[0] = '+' or '-' || '0' <= str[0] <= '9')
  or_exprt correct_first(
    or_exprt(starts_with_minus, starts_with_plus), starts_with_digit);
  axioms.push_back(implies_exprt(correct, correct_first));

  // correct => str[0]='+' or '-' ==> |str| > 1
  implies_exprt contains_digit(
    or_exprt(starts_with_minus, starts_with_plus),
    str.axiom_for_is_longer_than(from_integer(2, index_type)));
  axioms.push_back(implies_exprt(correct, contains_digit));

  // correct => |str| < max_size
  axioms.push_back(
    implies_exprt(correct, str.axiom_for_is_shorter_than(max_size)));

  // forall 1 <= qvar < |str| . correct => '0'<= str[qvar] <= '9'
  symbol_exprt qvar=fresh_univ_index("number_format", index_type);
  and_exprt is_digit(
    binary_relation_exprt(str[qvar], ID_ge, zero_char),
    binary_relation_exprt(str[qvar], ID_le, nine_char));
  string_constraintt all_digits(
    qvar, from_integer(1, index_type), str.length(), correct, is_digit);
  axioms.push_back(all_digits);

  return correct;
}

/// add axioms corresponding to the Integer.parseInt java function
/// \param f: function application with one string expression
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_parse_int(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  const typet &type=f.type();
  symbol_exprt i=fresh_symbol("parsed_int", type);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  exprt zero_char=constant_char('0', char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt plus_char=constant_char('+', char_type);
  assert(type.id()==ID_signedbv);
  exprt ten=from_integer(10, type);

  exprt chr=str[0];
  exprt starts_with_minus=equal_exprt(chr, minus_char);
  exprt starts_with_plus=equal_exprt(chr, plus_char);
  exprt starts_with_digit=binary_relation_exprt(chr, ID_ge, zero_char);

  // TODO: we should throw an exception when this does not hold:
  exprt correct=add_axioms_for_correct_number_format(str);
  axioms.push_back(correct);

  for(unsigned size=1; size<=10; size++)
  {
    exprt sum=from_integer(0, type);
    exprt first_value=typecast_exprt(minus_exprt(chr, zero_char), type);

    for(unsigned j=1; j<size; j++)
    {
      mult_exprt ten_sum(sum, ten);
      if(j>=9)
      {
        // We have to be careful about overflows
        div_exprt div(sum, ten);
        equal_exprt no_overflow(div, sum);
        axioms.push_back(no_overflow);
      }

      sum=plus_exprt_with_overflow_check(
        ten_sum,
        typecast_exprt(minus_exprt(str[j], zero_char), type));

      mult_exprt first(first_value, ten);
      if(j>=9)
      {
        // We have to be careful about overflows
        div_exprt div_first(first, ten);
        implies_exprt no_overflow_first(
          starts_with_digit, equal_exprt(div_first, first_value));
        axioms.push_back(no_overflow_first);
      }
      first_value=first;
    }

    // If the length is `size`, we add axioms:
    // a1 : starts_with_digit => i=sum+first_value
    // a2 : starts_with_plus => i=sum
    // a3 : starts_with_minus => i=-sum

    equal_exprt premise=str.axiom_for_has_length(size);
    implies_exprt a1(
      and_exprt(premise, starts_with_digit),
      equal_exprt(i, plus_exprt(sum, first_value)));
    axioms.push_back(a1);

    implies_exprt a2(and_exprt(premise, starts_with_plus), equal_exprt(i, sum));
    axioms.push_back(a2);

    implies_exprt a3(
      and_exprt(premise, starts_with_minus),
      equal_exprt(i, unary_minus_exprt(sum)));
    axioms.push_back(a3);
  }
  return i;
}
