/*******************************************************************\

Module: Generates string constraints for the family of indexOf and
        lastIndexOf java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_index_of

  Inputs:
    str - a string expression
    c - an expression representing a character
    from_index - an expression representing an index in the string

 Outputs: a integer expression

 Purpose: add axioms stating that the returned value is either:
          -1 if the string does not contain c
          an index greater than from_index such that the character of str at
          that position equals c and is the first occurence after from_index.

\*******************************************************************/

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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_index_of_string

  Inputs:
    haystack - a string expression
    substring - a string expression
    from_index - an expression representing an index in strings

 Outputs: an integer expression representing the first index of needle in
          haystack after from_index, or -1 if there is none

 Purpose: add axioms stating that the returned value is an index greater than
          from_index such that haystack at that index starts with needle and
          is the first occurence of needle in haystack after from_index,
          or returned value is -1 if haystack does not contain needle.

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_index_of_string(
  const string_exprt &haystack,
  const string_exprt &needle,
  const exprt &from_index)
{
  const typet &index_type=haystack.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => from_index <= offset <= |str|-|substring|
  // a2 : !contains <=> offset=-1
  // a3 : forall n:[0,|substring|[.
  //        contains => str[n+offset]=substring[n]
  // a4 : forall n:[from_index,offset[.
  //        contains => (exists m:[0,|substring|[. str[m+n]!=substring[m]])
  // a5:  forall n:[from_index,|str|-|substring|[.
  //        !contains => (exists m:[0,|substring|[. str[m+n]!=substring[m])

  implies_exprt a1(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, offset),
      binary_relation_exprt(
        offset, ID_le, minus_exprt(haystack.length(), needle.length()))));
  axioms.push_back(a1);

  equal_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  string_constraintt a3(
    qvar,
    needle.length(),
    contains,
    equal_exprt(haystack[plus_exprt(qvar, offset)], needle[qvar]));
  axioms.push_back(a3);

  if(!is_constant_string(needle))
  {
    // string_not contains_constraintt are formula of the form:
    // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]
    string_not_contains_constraintt a4(
      from_index,
      offset,
      contains,
      from_integer(0, index_type),
      needle.length(),
      haystack,
      needle);
    axioms.push_back(a4);

    string_not_contains_constraintt a5(
      from_index,
      minus_exprt(haystack.length(), needle.length()),
      not_exprt(contains),
      from_integer(0, index_type),
      needle.length(),
      haystack,
      needle);
    axioms.push_back(a5);
  }
  else
  {
    // Unfold the existential quantifier as a disjunction in case of a constant
    // a4 && a5 <=> a6:
    //  forall n:[from_index,|str|-|substring|].
    //    !contains || n < offset =>
    //       str[n]!=substring[0] || ... ||
    //       str[n+|substring|-1]!=substring[|substring|-1]
    symbol_exprt qvar2=fresh_univ_index("QA_index_of_string_2", index_type);
    mp_integer sub_length;
    assert(!to_integer(needle.length(), sub_length));
    exprt::operandst disjuncts;
    for(mp_integer offset=0; offset<sub_length; ++offset)
    {
      exprt expr_offset=from_integer(offset, index_type);
      plus_exprt shifted(expr_offset, qvar2);
      disjuncts.push_back(
        not_exprt(equal_exprt(haystack[shifted], needle[expr_offset])));
    }

    or_exprt premise(
      not_exprt(contains), binary_relation_exprt(qvar, ID_lt, offset));
    minus_exprt length_diff(haystack.length(), needle.length());
    string_constraintt a6(
      qvar2,
      from_index,
      plus_exprt(from_integer(1, index_type), length_diff),
      premise,
      disjunction(disjuncts));
    axioms.push_back(a6);
  }

  return offset;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_last_index_of_string

  Inputs:
    str - a string expression
    substring - a string expression
    from_index - an expression representing an index in strings

 Outputs: an integer expression representing the last index of needle in
          haystack after from_index, or -1 if there is none

 Purpose: add axioms stating that the returned value is an index less than
          from_index such that str at that index starts with substring and is
          the last occurence of substring in str before from_index,
          or the returned value is -1 if str does not contain substring.

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_last_index_of_string(
  const string_exprt &haystack,
  const string_exprt &needle,
  const exprt &from_index)
{
  const typet &index_type=haystack.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => |substring| >= length && offset <= from_index
  // a2 : !contains <=> offset=-1
  // a3 : forall n:[0, substring.length[,
  //        contains => str[n+offset]=substring[n]
  // a4 : forall n:[offset+1, min(from_index, |str| - |substring|)].
  //        contains =>
  //          (exists m:[0,|substring|[. str[m+n]!=substring[m]])
  // a5:  forall n:[0, min(from_index, |str| - |substring|)].
  //        !contains =>
  //          (exists m:[0,|substring|[. str[m+n]!=substring[m])

  implies_exprt a1(
    contains,
    and_exprt(
      haystack.axiom_for_is_longer_than(
        plus_exprt_with_overflow_check(needle.length(), offset)),
      binary_relation_exprt(offset, ID_le, from_index)));
  axioms.push_back(a1);

  equal_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  equal_exprt constr3(haystack[plus_exprt(qvar, offset)], needle[qvar]);
  string_constraintt a3(qvar, needle.length(), contains, constr3);
  axioms.push_back(a3);

  // end_index is min(from_index, |str| - |substring|)
  minus_exprt length_diff(haystack.length(), needle.length());
  if_exprt end_index(
    binary_relation_exprt(from_index, ID_le, length_diff),
    from_index,
    length_diff);

  if(!is_constant_string(needle))
  {
    string_not_contains_constraintt a4(
      plus_exprt(offset, from_integer(1, index_type)),
      from_index,
      plus_exprt(end_index, from_integer(1, index_type)),
      from_integer(0, index_type),
      needle.length(),
      haystack,
      needle);
    axioms.push_back(a4);

    string_not_contains_constraintt a5(
      from_integer(0, index_type),
      plus_exprt(end_index, from_integer(1, index_type)),
      not_exprt(contains),
      from_integer(0, index_type),
      needle.length(),
      haystack,
      needle);
    axioms.push_back(a5);
  }
  else
  {
    // Unfold the existential quantifier as a disjunction in case of a constant
    // a4 && a5 <=> a6:
    //  forall n:[0, min(from_index,|str|-|substring|)].
    //    !contains || n > offset =>
    //       str[n]!=substring[0] || ... ||
    //       str[n+|substring|-1]!=substring[|substring|-1]
    symbol_exprt qvar2=fresh_univ_index("QA_index_of_string_2", index_type);
    mp_integer sub_length;
    assert(!to_integer(needle.length(), sub_length));
    exprt::operandst disjuncts;
    for(mp_integer offset=0; offset<sub_length; ++offset)
    {
      exprt expr_offset=from_integer(offset, index_type);
      plus_exprt shifted(expr_offset, qvar2);
      disjuncts.push_back(
        not_exprt(equal_exprt(haystack[shifted], needle[expr_offset])));
    }

    or_exprt premise(
      not_exprt(contains), binary_relation_exprt(qvar, ID_gt, offset));
    string_constraintt a6(
      qvar2,
      from_index,
      plus_exprt(from_integer(1, index_type), end_index),
      premise,
      disjunction(disjuncts));
    axioms.push_back(a6);
  }

  return offset;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_index_of

  Inputs: function application with 2 or 3 arguments

 Outputs: a integer expression

 Purpose: add axioms corresponding to the String.indexOf:(C),
          String.indexOf:(CI), String.indexOf:(String), and
          String.indexOf:(String,I) java functions

\*******************************************************************/

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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_last_index_of

  Inputs:
    str - a string expression
    c - an expression representing a character
    from_index - an expression representing an index in the string

 Outputs: a integer expression

 Purpose: add axioms stating that the returned value is either:
          -1 if the string does not contain c
          an index less than from_index such that the character of str at
          that position equals c and is the last occurence before from_index.

\*******************************************************************/

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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_last_index_of

  Inputs: function application with 2 or 3 arguments

 Outputs: a integer expression

 Purpose: add axioms corresponding to the String.lastIndexOf:(C),
          String.lastIndexOf:(CI), String.lastIndexOf:(String), and
          String.lastIndexOf:(String,I) java functions

\*******************************************************************/

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
