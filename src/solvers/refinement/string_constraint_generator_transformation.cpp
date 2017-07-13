/*******************************************************************\

Module: Generates string constraints for string transformations,
        that is, functions taking one string and returning another

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string transformations, that is, functions
///   taking one string and returning another

#include <solvers/refinement/string_constraint_generator.h>

/// add axioms to say that the returned string expression has length given by
/// the second argument and whose characters are equal to those of the first
/// argument for the positions which are defined in both strings
/// \par parameters: function application with two arguments, the first of which
///   is
/// a string and the second an integer which should have same type has
/// return by get_index_type()
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_set_length(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  exprt k=args(f, 2)[1];
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : |res|=k
  // a2 : forall i<k. (i<k ==> s[i]=s1[i]) &&(i >= k ==> s[i]=0)

  axioms.push_back(res.axiom_for_has_length(k));

  symbol_exprt idx=fresh_univ_index(
    "QA_index_set_length", ref_type.get_index_type());
  string_constraintt a2(
    idx, k, and_exprt(
      implies_exprt(
        s1.axiom_for_is_strictly_longer_than(idx),
        equal_exprt(s1[idx], res[idx])),
      implies_exprt(
        s1.axiom_for_is_shorter_than(idx),
        equal_exprt(s1[idx], constant_char(0, ref_type.get_char_type())))));
  axioms.push_back(a2);

  return res;
}


/// add axioms corresponding to the String.substring java function Warning: the
/// specification may not be correct for the case where the string is shorter
/// than the end index
/// \par parameters: function application with one string argument, one start
///   index
/// argument and an optional end index argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_substring(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()>=2);
  string_exprt str=get_string_expr(args[0]);
  exprt i(args[1]);
  exprt j;
  if(args.size()==3)
  {
    j=args[2];
  }
  else
  {
    assert(args.size()==2);
    j=str.length();
  }
  return add_axioms_for_substring(str, i, j);
}

/// add axioms stating that the returned string expression is equal to the input
/// one starting at `start` and ending before `end`
/// \par parameters: a string expression, an expression for the start index, and
///   an
/// expression for the end index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_substring(
  const string_exprt &str, const exprt &start, const exprt &end)
{
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &index_type=ref_type.get_index_type();
  assert(start.type()==index_type);
  assert(end.type()==index_type);
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : start < end => |res| = end - start
  // a2 : start >= end => |res| = 0
  // a3 : |str| > end
  // a4 : forall idx<str.length, str[idx]=arg_str[idx+i]

  implies_exprt a1(
    binary_relation_exprt(start, ID_lt, end),
    res.axiom_for_has_length(minus_exprt(end, start)));
  axioms.push_back(a1);

  exprt is_empty=res.axiom_for_has_length(from_integer(0, index_type));
  implies_exprt a2(binary_relation_exprt(start, ID_ge, end), is_empty);
  axioms.push_back(a2);

  // Warning: check what to do if the string is not long enough
  axioms.push_back(str.axiom_for_is_longer_than(end));

  symbol_exprt idx=fresh_univ_index("QA_index_substring", index_type);
  string_constraintt a4(idx,
                        res.length(),
                        equal_exprt(res[idx],
                        str[plus_exprt_with_overflow_check(start, idx)]));
  axioms.push_back(a4);
  return res;
}

/// add axioms corresponding to the String.trim java function
/// \par parameters: function application with one string argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_trim(
  const function_application_exprt &expr)
{
  string_exprt str=get_string_expr(args(expr, 1)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &index_type=ref_type.get_index_type();
  string_exprt res=fresh_string(ref_type);
  symbol_exprt idx=fresh_exist_index("index_trim", index_type);
  exprt space_char=constant_char(' ', ref_type.get_char_type());

  // We add axioms:
  // a1 : m + |s1| <= |str|
  // a2 : idx >= 0
  // a3 : str >= idx
  // a4 : |res|>= 0
  // a5 : |res|<=|str|
  //        (this is necessary to prevent exceeding the biggest integer)
  // a6 : forall n<m, str[n]<=' '
  // a7 : forall n<|str|-m-|s1|, str[m+|s1|+n]<=' '
  // a8 : forall n<|s1|, s[idx+n]=s1[n]
  // a9 : (s[m]>' ' &&s[m+|s1|-1]>' ') || m=|s|

  exprt a1=str.axiom_for_is_longer_than(
    plus_exprt_with_overflow_check(idx, res.length()));
  axioms.push_back(a1);

  binary_relation_exprt a2(idx, ID_ge, from_integer(0, index_type));
  axioms.push_back(a2);

  exprt a3=str.axiom_for_is_longer_than(idx);
  axioms.push_back(a3);

  exprt a4=res.axiom_for_is_longer_than(
    from_integer(0, index_type));
  axioms.push_back(a4);

  exprt a5=res.axiom_for_is_shorter_than(str);
  axioms.push_back(a5);

  symbol_exprt n=fresh_univ_index("QA_index_trim", index_type);
  binary_relation_exprt non_print(str[n], ID_le, space_char);
  string_constraintt a6(n, idx, non_print);
  axioms.push_back(a6);

  symbol_exprt n2=fresh_univ_index("QA_index_trim2", index_type);
  minus_exprt bound(str.length(), plus_exprt_with_overflow_check(idx,
                                                                 res.length()));
  binary_relation_exprt eqn2(
    str[plus_exprt(idx, plus_exprt(res.length(), n2))],
    ID_le,
    space_char);

  string_constraintt a7(n2, bound, eqn2);
  axioms.push_back(a7);

  symbol_exprt n3=fresh_univ_index("QA_index_trim3", index_type);
  equal_exprt eqn3(res[n3], str[plus_exprt(n3, idx)]);
  string_constraintt a8(n3, res.length(), eqn3);
  axioms.push_back(a8);

  minus_exprt index_before(
    plus_exprt_with_overflow_check(idx, res.length()),
      from_integer(1, index_type));
  binary_relation_exprt no_space_before(str[index_before], ID_gt, space_char);
  or_exprt a9(
    equal_exprt(idx, str.length()),
    and_exprt(
      binary_relation_exprt(str[idx], ID_gt, space_char),
      no_space_before));
  axioms.push_back(a9);
  return res;
}

/// add axioms corresponding to the String.toLowerCase java function
/// \par parameters: function application with one string argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_to_lower_case(
  const function_application_exprt &expr)
{
  string_exprt str=get_string_expr(args(expr, 1)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  string_exprt res=fresh_string(ref_type);
  exprt char_a=constant_char('a', char_type);
  exprt char_A=constant_char('A', char_type);
  exprt char_z=constant_char('z', char_type);
  exprt char_Z=constant_char('Z', char_type);

  // TODO: add support for locales using case mapping information
  // from the UnicodeData file.

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall idx<str.length, 'A'<=str[idx]<='Z' => res[idx]=str[idx]+'a'-'A'
  // a3 : forall idx<str.length, !('a'<=str[idx]<='z') => res[idx]=str[idx]
  // forall idx<str.length,
  // this[idx]='A'<=str[idx]<='Z' ? str[idx]+'a'-'A' : str[idx]

  exprt a1=res.axiom_for_has_same_length_as(str);
  axioms.push_back(a1);

  symbol_exprt idx=fresh_univ_index("QA_lower_case", index_type);
  exprt is_upper_case=and_exprt(
    binary_relation_exprt(char_A, ID_le, str[idx]),
    binary_relation_exprt(str[idx], ID_le, char_Z));
  minus_exprt diff(char_a, char_A);
  equal_exprt convert(res[idx], plus_exprt(str[idx], diff));
  string_constraintt a2(idx, res.length(), is_upper_case, convert);
  axioms.push_back(a2);

  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a3(idx, res.length(), not_exprt(is_upper_case), eq);
  axioms.push_back(a3);
  return res;
}

/// add axioms corresponding to the String.toUpperCase java function
/// \par parameters: function application with one string argument
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_to_upper_case(
  const function_application_exprt &expr)
{
  string_exprt str=get_string_expr(args(expr, 1)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  string_exprt res=fresh_string(ref_type);
  exprt char_a=constant_char('a', char_type);
  exprt char_A=constant_char('A', char_type);
  exprt char_z=constant_char('z', char_type);
  exprt char_Z=constant_char('Z', char_type);

  // TODO: add support for locales using case mapping information
  // from the UnicodeData file.

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall idx<str.length, 'a'<=str[idx]<='z' => res[idx]=str[idx]+'A'-'a'
  // a3 : forall idx<str.length, !('a'<=str[idx]<='z') => res[idx]=str[idx]

  exprt a1=res.axiom_for_has_same_length_as(str);
  axioms.push_back(a1);

  symbol_exprt idx=fresh_univ_index("QA_upper_case", index_type);
  exprt is_lower_case=and_exprt(
    binary_relation_exprt(char_a, ID_le, str[idx]),
    binary_relation_exprt(str[idx], ID_le, char_z));
  minus_exprt diff(char_A, char_a);
  equal_exprt convert(res[idx], plus_exprt(str[idx], diff));
  string_constraintt a2(idx, res.length(), is_lower_case, convert);
  axioms.push_back(a2);

  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a3(idx, res.length(), not_exprt(is_lower_case), eq);
  axioms.push_back(a3);
  return res;
}


/// add axioms corresponding stating that the result is similar to that of the
/// StringBuilder.setCharAt java function Warning: this may be underspecified in
/// the case wher the index exceed the length of the string
/// \par parameters: function application with three arguments, the first is a
///   string
/// the second an index and the third a character
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_char_set(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 3)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  string_exprt res=fresh_string(ref_type);
  with_exprt sarrnew(str.content(), args(f, 3)[1], args(f, 3)[2]);

  // We add axiom:
  // a1 : arg1 < |str| => res = str with [arg1]=arg2

  implies_exprt a1(
    binary_relation_exprt(args(f, 3)[1], ID_lt, str.length()),
    and_exprt(
      equal_exprt(res.content(), sarrnew),
      res.axiom_for_has_same_length_as(str)));
  axioms.push_back(a1);
  return res;
}

/// add axioms corresponding to the String.replace java function
/// \par parameters: function application with three arguments, the first is a
///   string,
/// the second and the third are characters
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_replace(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 3)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const exprt &old_char=args(f, 3)[1];
  const exprt &new_char=args(f, 3)[2];
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall qvar, 0<=qvar<|res|,
  //    str[qvar]=oldChar => res[qvar]=newChar
  //    !str[qvar]=oldChar => res[qvar]=str[qvar]

  axioms.push_back(res.axiom_for_has_same_length_as(str));

  symbol_exprt qvar=fresh_univ_index("QA_replace", ref_type.get_index_type());
  implies_exprt case1(
    equal_exprt(str[qvar], old_char),
    equal_exprt(res[qvar], new_char));
  implies_exprt case2(
    not_exprt(equal_exprt(str[qvar], old_char)),
    equal_exprt(res[qvar], str[qvar]));
  string_constraintt a2(qvar, res.length(), and_exprt(case1, case2));
  axioms.push_back(a2);
  return res;
}

/// add axioms corresponding to the StringBuilder.deleteCharAt java function
/// \par parameters: function application with two arguments, the first is a
///   string
/// and the second is an index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_delete_char_at(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 2)[0]);
  exprt index_one=from_integer(1, str.length().type());
  return add_axioms_for_delete(
    str,
    args(f, 2)[1],
    plus_exprt_with_overflow_check(args(f, 2)[1], index_one));
}

/// add axioms stating that the returned string corresponds to the input one
/// where we removed characters between the positions start (included) and end
/// (not included)
/// \par parameters: a string expression, a start index and an end index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_delete(
  const string_exprt &str, const exprt &start, const exprt &end)
{
  assert(start.type()==str.length().type());
  assert(end.type()==str.length().type());
  string_exprt str1=add_axioms_for_substring(
    str, from_integer(0, str.length().type()), start);
  string_exprt str2=add_axioms_for_substring(str, end, str.length());
  return add_axioms_for_concat(str1, str2);
}

/// add axioms corresponding to the StringBuilder.delete java function
/// \par parameters: function application with three arguments: a string
/// expression, a start index and an end index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_delete(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 3)[0]);
  return add_axioms_for_delete(str, args(f, 3)[1], args(f, 3)[2]);
}
