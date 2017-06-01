/*******************************************************************\

Module: Generates string constraints for functions adding content
        add the end of strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_substr

  Inputs:
    s1 - string expression
    s2 - string expression
    start_index - expression representing an integer
    end_index - expression representing an integer

 Outputs: a new string expression

 Purpose: add axioms to say that the returned string expression is equal to
          the concatenation of s1 with the substring of s2 starting at index
          start_index and ending at index end_index

    TODO: for now it just assumes start_index <= end_index < s2.length

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_substr(
  const string_exprt &s1,
  const string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index)
{
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : end_index > start_index => |res|=|s1|+ end_index - start_index
  // a2 : end_index <= start_index => res = s1
  // a3 : forall i<|s1|. res[i]=s1[i]
  // a4 : forall i< end_index - start_index. res[i+|s1|]=s2[start_index+i]

  binary_relation_exprt prem(end_index, ID_gt, start_index);

  exprt res_length=plus_exprt_with_overflow_check(
    s1.length(), minus_exprt(end_index, start_index));
  implies_exprt a1(prem, equal_exprt(res.length(), res_length));
  axioms.push_back(a1);

  implies_exprt a2(not_exprt(prem), equal_exprt(res.length(), s1.length()));
  axioms.push_back(a2);

  symbol_exprt idx=fresh_univ_index("QA_index_concat", res.length().type());
  string_constraintt a3(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a3);

  symbol_exprt idx2=fresh_univ_index("QA_index_concat2", res.length().type());
  equal_exprt res_eq(
    res[plus_exprt(idx2, s1.length())], s2[plus_exprt(start_index, idx2)]);
  string_constraintt a4(idx2, minus_exprt(end_index, start_index), res_eq);
  axioms.push_back(a4);

  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat

  Inputs: two string expressions

 Outputs: a new string expression

 Purpose: add axioms to say that the returned string expression is equal to
          the concatenation of the two string expressions given as input

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat(
  const string_exprt &s1, const string_exprt &s2)
{
  exprt index_zero=from_integer(0, s2.length().type());
  return add_axioms_for_concat_substr(s1, s2, index_zero, s2.length());
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat

  Inputs: function application with two arguments which are strings

 Outputs: a new string expression

 Purpose: add axioms to say that the returned string expression is equal to
          the concatenation of the two string arguments of
          the function application.
          In case 4 arguments instead of 2 are given the last two arguments
          are intepreted as a start index and last index from which we extract
          a substring of the second argument: this is similar to the
          Java StringBuiledr.append(CharSequence s, int start, int end) method.

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()>=2);
  string_exprt s1=get_string_expr(args[0]);
  string_exprt s2=get_string_expr(args[1]);
  if(args.size()!=2)
  {
    assert(args.size()==4);
    return add_axioms_for_concat_substr(s1, s2, args[2], args[3]);
  }
  else
    return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_int

  Inputs: function application with two arguments: a string and an integer

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.append(I) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_int(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(
    args(f, 2)[1], MAX_INTEGER_LENGTH, ref_type);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_long

  Inputs: function application with two arguments: a string and a
          integer of type long

 Outputs: a new string expression

 Purpose: Add axioms corresponding to the StringBuilder.append(J) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_long(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 2)[1], MAX_LONG_LENGTH, ref_type);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_bool

  Inputs: function application two arguments: a string and a bool

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.append(Z) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_bool(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_from_bool(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_char

  Inputs: function application with two arguments: a string and a char

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.append(C) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_char(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_from_char(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_double

  Inputs: function application with two arguments: a string and a double

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.append(D) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_double(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  assert(refined_string_typet::is_refined_string_type(f.type()));
  refined_string_typet ref_type=to_refined_string_type(f.type());
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], ref_type, true);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_float

  Inputs: function application with two arguments: a string and a float

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.append(F) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_float(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  assert(refined_string_typet::is_refined_string_type(f.type()));
  refined_string_typet ref_type=to_refined_string_type(f.type());
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], ref_type, false);
  return add_axioms_for_concat(s1, s2);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_concat_code_point

  Inputs: function application with two arguments: a string and a code point

 Outputs: a new string expression

 Purpose: Add axioms corresponding to the StringBuilder.appendCodePoint(I)
          function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_concat_code_point(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_for_code_point(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}
