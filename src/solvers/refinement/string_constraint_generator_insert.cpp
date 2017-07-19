/*******************************************************************\

Module: Generates string constraints for the family of insert Java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of insert Java functions

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>

/// add axioms stating that the result correspond to the first string where we
/// inserted the second one at possition offset
/// \par parameters: two string expression and an integer offset
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert(
  const string_exprt &s1, const string_exprt &s2, const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());
  string_exprt pref=add_axioms_for_substring(
    s1, from_integer(0, offset.type()), offset);
  string_exprt suf=add_axioms_for_substring(s1, offset, s1.length());
  string_exprt concat1=add_axioms_for_concat(pref, s2);
  return add_axioms_for_concat(concat1, suf);
}

/// add axioms corresponding to the StringBuilder.insert(int, CharSequence) and
/// StringBuilder.insert(int, CharSequence, int, int) java functions
/// \par parameters: function application with three arguments: two strings and
///   an index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()>=3);
  string_exprt s1=get_string_expr(f.arguments()[0]);
  string_exprt s2=get_string_expr(f.arguments()[2]);
  const exprt &offset=f.arguments()[1];
  if(f.arguments().size()==5)
  {
    const exprt &start=f.arguments()[3];
    const exprt &end=f.arguments()[4];
    string_exprt substring=add_axioms_for_substring(s2, start, end);
    return add_axioms_for_insert(s1, substring, offset);
  }
  else
  {
    INVARIANT(
      f.arguments().size()==3,
      string_refinement_invariantt("f must have 2 or 5 arguments and the case "
        "of 5 arguments is already handled"));
    return add_axioms_for_insert(s1, s2, offset);
  }
}

/// add axioms corresponding to the StringBuilder.insert(I) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset, and an integer
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_int(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(
    args(f, 3)[2], MAX_INTEGER_LENGTH, ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert(J) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset and a long
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_long(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 3)[2], MAX_LONG_LENGTH, ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert(Z) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset, and a Boolean
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_bool(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_bool(args(f, 3)[2], ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert(C) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset, and a character
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_char(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_from_char(args(f, 3)[2], ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert(D) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset, and a double
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_double(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_for_string_of_float(args(f, 3)[2], ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert(F) java function
/// \par parameters: function application with three arguments: a string, an
///   integer
/// offset, and a float
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_float(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 3)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt s2=add_axioms_for_string_of_float(args(f, 3)[2], ref_type);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/// add axioms corresponding to the StringBuilder.insert:(I[CII) and
/// StringBuilder.insert:(I[C) java functions
/// \par parameters: function application with 4 arguments plus two optional
///   arguments:
/// a string, an offset index, a length, data array, an offset and a
/// count
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_insert_char_array(
  const function_application_exprt &f)
{
  exprt offset;
  exprt count;
  if(f.arguments().size()==6)
  {
    offset=f.arguments()[4];
    count=f.arguments()[5];
  }
  else
  {
    INVARIANT(
      f.arguments().size()==4,
      string_refinement_invariantt("f must have 4 or 6 arguments and the case "
        "of 6 arguments is already handled"));
    count=f.arguments()[2];
    offset=from_integer(0, count.type());
  }

  string_exprt str=get_string_expr(f.arguments()[0]);
  const exprt &length=f.arguments()[2];
  const exprt &data=f.arguments()[3];
  string_exprt arr=add_axioms_from_char_array(
    length, data, offset, count);
  return add_axioms_for_insert(str, arr, f.arguments()[1]);
}
