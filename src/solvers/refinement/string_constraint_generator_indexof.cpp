/*******************************************************************\

Module: Generates string constraints for the family of indexOf and
        lastIndexOf java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of indexOf and lastIndexOf java
///   functions

#include <solvers/refinement/string_constraint_generator.h>

/// add axioms that the returned value is either -1 or greater than from_index
/// and the character at that position equals to c
/// \par parameters: a string expression, a character expression and an integer
///   expression
/// \return a integer expression
exprt string_constraint_generatort::add_axioms_for_index_of(
  const string_exprt &str, const exprt &c, const exprt &from_index)
{
  const typet &index_type=str.length().type();
  symbol_exprt index=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_in_index_of");

  // We add axioms:
  // a1 : -1 <= index<|str|
  // a2 : !contains <=> index=-1
  // a3 : contains => from_index<=index&&str[index]=c
  // a4 : forall n, from_index<=n<index. contains => str[n]!=c
  // a5 : forall m, from_index<=n<|str|. !contains => str[m]!=c

  exprt minus1=from_integer(-1, index_type);
  and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_lt, str.length()));
  axioms.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  axioms.push_back(a2);

  implies_exprt a3(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, index),
      equal_exprt(str[index], c)));
  axioms.push_back(a3);

  symbol_exprt n=fresh_univ_index("QA_index_of", index_type);
  string_constraintt a4(
    n, from_index, index, contains, not_exprt(equal_exprt(str[n], c)));
  axioms.push_back(a4);

  symbol_exprt m=fresh_univ_index("QA_index_of", index_type);
  string_constraintt a5(
    m,
    from_index,
    str.length(),
    not_exprt(contains),
    not_exprt(equal_exprt(str[m], c)));
  axioms.push_back(a5);

  return index;
}

/// add axioms stating that the returned value is either -1 or greater than
/// from_index and the string beggining there has prefix substring
/// \par parameters: two string expressions and an integer expression
/// \return a integer expression
exprt string_constraint_generatort::add_axioms_for_index_of_string(
  const string_exprt &str,
  const string_exprt &substring,
  const exprt &from_index)
{
  const typet &index_type=str.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => |str|-|substring|>=offset>=from_index
  // a2 : !contains => offset=-1
  // a3 : forall 0<=witness<|substring|.
  //        contains => str[witness+offset]=substring[witness]

  implies_exprt a1(
    contains,
    and_exprt(
      str.axiom_for_is_longer_than(plus_exprt_with_overflow_check(
        substring.length(), offset)),
      binary_relation_exprt(offset, ID_ge, from_index)));
  axioms.push_back(a1);

  implies_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  string_constraintt a3(
    qvar,
    substring.length(),
    contains,
    equal_exprt(str[plus_exprt(qvar, offset)], substring[qvar]));
  axioms.push_back(a3);

  return offset;
}

exprt string_constraint_generatort::add_axioms_for_last_index_of_string(
  const string_exprt &str,
  const string_exprt &substring,
  const exprt &from_index)
{
  const typet &index_type=str.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => |substring| >= length &&offset <= from_index
  // a2 : !contains => offset=-1
  // a3 : forall 0 <= witness<substring.length,
  //        contains => str[witness+offset]=substring[witness]

  implies_exprt a1(
    contains,
    and_exprt(
      str.axiom_for_is_longer_than(
        plus_exprt_with_overflow_check(substring.length(), offset)),
      binary_relation_exprt(offset, ID_le, from_index)));
  axioms.push_back(a1);

  implies_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  equal_exprt constr3(str[plus_exprt(qvar, offset)], substring[qvar]);
  string_constraintt a3(qvar, substring.length(), contains, constr3);
  axioms.push_back(a3);

  return offset;
}

/// add axioms corresponding to the String.indexOf:(C), String.indexOf:(CI),
/// String.indexOf:(String), and String.indexOf:(String,I) java functions
/// \par parameters: function application with 2 or 3 arguments
/// \return a integer expression
exprt string_constraint_generatort::add_axioms_for_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  string_exprt str=get_string_expr(args[0]);
  const exprt &c=args[1];
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  assert(f.type()==ref_type.get_index_type());
  exprt from_index;

  if(args.size()==2)
    from_index=from_integer(0, ref_type.get_index_type());
  else if(args.size()==3)
    from_index=args[2];
  else
    assert(false);

  if(c.type().id()==ID_unsignedbv || c.type().id()==ID_signedbv)
  {
    return add_axioms_for_index_of(
      str, typecast_exprt(c, ref_type.get_char_type()), from_index);
  }
  else
  {
    assert(refined_string_typet::is_refined_string_type(c.type()));
    string_exprt sub=get_string_expr(c);
    return add_axioms_for_index_of_string(str, sub, from_index);
  }
}

exprt string_constraint_generatort::add_axioms_for_last_index_of(
  const string_exprt &str, const exprt &c, const exprt &from_index)
{
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &index_type=ref_type.get_index_type();
  symbol_exprt index=fresh_exist_index("last_index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_in_last_index_of");

  // We add axioms:
  // a1 : -1 <= i <= from_index
  // a2 : (i=-1 <=> !contains)
  // a3 : (contains => i <= from_index &&s[i]=c)
  // a4 : forall n. i+1 <= n < from_index +1 &&contains => s[n]!=c
  // a5 : forall m. 0 <= m < from_index +1 &&!contains => s[m]!=c

  exprt index1=from_integer(1, index_type);
  exprt minus1=from_integer(-1, index_type);
  exprt from_index_plus_one=plus_exprt_with_overflow_check(from_index, index1);
  and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_lt, from_index_plus_one));
  axioms.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  axioms.push_back(a2);

  implies_exprt a3(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_ge, index),
      equal_exprt(str[index], c)));
  axioms.push_back(a3);

  symbol_exprt n=fresh_univ_index("QA_last_index_of", index_type);
  string_constraintt a4(
    n,
    plus_exprt(index, index1),
    from_index_plus_one,
    contains,
    not_exprt(equal_exprt(str[n], c)));
  axioms.push_back(a4);

  symbol_exprt m=fresh_univ_index("QA_last_index_of", index_type);
  string_constraintt a5(
    m,
    from_index_plus_one,
    not_exprt(contains),
    not_exprt(equal_exprt(str[m], c)));
  axioms.push_back(a5);

  return index;
}

/// add axioms corresponding to the String.lastIndexOf:(C),
/// String.lastIndexOf:(CI), String.lastIndexOf:(String), and
/// String.lastIndexOf:(String,I) java functions
/// \par parameters: function application with 2 or 3 arguments
/// \return a integer expression
exprt string_constraint_generatort::add_axioms_for_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  string_exprt str=get_string_expr(args[0]);
  exprt c=args[1];
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  exprt from_index;
  assert(f.type()==ref_type.get_index_type());

  if(args.size()==2)
    from_index=minus_exprt(str.length(), from_integer(1, str.length().type()));
  else if(args.size()==3)
    from_index=args[2];
  else
    assert(false);

  if(c.type().id()==ID_unsignedbv || c.type().id()==ID_signedbv)
  {
    return add_axioms_for_last_index_of(
      str, typecast_exprt(c, ref_type.get_char_type()), from_index);
  }
  else
  {
    string_exprt sub=get_string_expr(c);
    return add_axioms_for_last_index_of_string(str, sub, from_index);
  }
}
