/*******************************************************************\

Module: Generates string constraints for functions adding content
        add the end of strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions adding content add the end of
///   strings

#include <solvers/refinement/string_constraint_generator.h>

/// add axioms to say that the returned string expression is equal to the
/// concatenation of the two string expressions given as input
/// \par parameters: two string expressions
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat(
  const string_exprt &s1, const string_exprt &s2)
{
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : |res|=|s1|+|s2|
  // a2 : |s1| <= |res| (to avoid overflow with very long strings)
  // a3 : |s2| <= |res| (to avoid overflow with very long strings)
  // a4 : forall i<|s1|. res[i]=s1[i]
  // a5 : forall i<|s2|. res[i+|s1|]=s2[i]

  equal_exprt a1(
    res.length(), plus_exprt_with_overflow_check(s1.length(), s2.length()));
  axioms.push_back(a1);
  axioms.push_back(s1.axiom_for_is_shorter_than(res));
  axioms.push_back(s2.axiom_for_is_shorter_than(res));

  symbol_exprt idx=fresh_univ_index("QA_index_concat", res.length().type());
  string_constraintt a4(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a4);

  symbol_exprt idx2=fresh_univ_index("QA_index_concat2", res.length().type());
  equal_exprt res_eq(s2[idx2], res[plus_exprt(idx2, s1.length())]);
  string_constraintt a5(idx2, s2.length(), res_eq);
  axioms.push_back(a5);

  return res;
}

/// add axioms to say that the returned string expression is equal to the
/// concatenation of the two string arguments of the function application
/// \par parameters: function application with two arguments which are strings
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2);

  string_exprt s1=get_string_expr(args[0]);
  string_exprt s2=get_string_expr(args[1]);

  return add_axioms_for_concat(s1, s2);
}

/// add axioms corresponding to the StringBuilder.append(I) java function
/// \par parameters: function application with two arguments: a string and an
///   integer
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_int(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(
    args(f, 2)[1], MAX_INTEGER_LENGTH, ref_type);
  return add_axioms_for_concat(s1, s2);
}

/// Add axioms corresponding to the StringBuilder.append(J) java function
/// \par parameters: function application with two arguments: a string and a
/// integer of type long
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_long(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 2)[1], MAX_LONG_LENGTH, ref_type);
  return add_axioms_for_concat(s1, s2);
}

/// add axioms corresponding to the StringBuilder.append(Z) java function
/// \par parameters: function application two arguments: a string and a bool
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_bool(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_from_bool(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}

/// add axioms corresponding to the StringBuilder.append(C) java function
/// \par parameters: function application with two arguments: a string and a
///   char
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_char(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_from_char(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}

/// add axioms corresponding to the StringBuilder.append(D) java function
/// \par parameters: function application with two arguments: a string and a
///   double
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_double(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  assert(refined_string_typet::is_refined_string_type(f.type()));
  refined_string_typet ref_type=to_refined_string_type(f.type());
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], ref_type, true);
  return add_axioms_for_concat(s1, s2);
}

/// add axioms corresponding to the StringBuilder.append(F) java function
/// \par parameters: function application with two arguments: a string and a
///   float
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_float(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  assert(refined_string_typet::is_refined_string_type(f.type()));
  refined_string_typet ref_type=to_refined_string_type(f.type());
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], ref_type, false);
  return add_axioms_for_concat(s1, s2);
}

/// Add axioms corresponding to the StringBuilder.appendCodePoint(I) function
/// \par parameters: function application with two arguments: a string and a
///   code point
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_concat_code_point(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_for_code_point(args(f, 2)[1], ref_type);
  return add_axioms_for_concat(s1, s2);
}
