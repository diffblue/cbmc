/*******************************************************************\

Module: Generates string constraints for the family of insert Java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert

  Inputs: two string expression and an integer offset

 Outputs: a new string expression

 Purpose: add axioms stating that the result correspond to the first string
          where we inserted the second one at possition offset

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert(
  const string_exprt &s1, const string_exprt &s2, const exprt &offset)
{
  assert(offset.type()==get_index_type());
  string_exprt pref=add_axioms_for_substring(
    s1, from_integer(0, get_index_type()), offset);
  string_exprt suf=add_axioms_for_substring(s1, offset, s1.length());
  string_exprt concat1=add_axioms_for_concat(pref, s2);
  return add_axioms_for_concat(concat1, suf);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert

  Inputs: function application with three arguments: two strings and an index

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(String) java
          function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_int

  Inputs: function application with three arguments: a string, an integer
          offset, and an integer

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(I) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_int(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 3)[2], MAX_INTEGER_LENGTH);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_long

  Inputs: function application with three arguments: a string, an integer
          offset and a long

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(J) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_long(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 3)[2], MAX_LONG_LENGTH);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_bool

  Inputs: function application with three arguments: a string, an integer
          offset, and a Boolean

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(Z) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_bool(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_bool(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_char

  Inputs: function application with three arguments: a string, an integer
          offset, and a character

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(C) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_char(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_char(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_double

  Inputs: function application with three arguments: a string, an integer
          offset, and a double

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(D) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_double(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_float

  Inputs: function application with three arguments: a string, an integer
          offset, and a float

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert(F) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_insert_float(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_insert_char_array

  Inputs: function application with 4 arguments plus two optional arguments:
          a string, an offset index, a length, data array, an offset and a
          count

 Outputs: a new string expression

 Purpose: add axioms corresponding to the StringBuilder.insert:(I[CII)
          and StringBuilder.insert:(I[C) java functions

\*******************************************************************/

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
    assert(f.arguments().size()==4);
    count=f.arguments()[2];
    offset=from_integer(0, get_index_type());
  }

  string_exprt str=add_axioms_for_string_expr(f.arguments()[0]);
  const exprt &length=f.arguments()[2];
  const exprt &data=f.arguments()[3];
  string_exprt arr=add_axioms_from_char_array(
    length, data, offset, count);
  return add_axioms_for_insert(str, arr, f.arguments()[1]);
}
