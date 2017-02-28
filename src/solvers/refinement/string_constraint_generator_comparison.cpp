/*******************************************************************\

Module: Generates string constraints for function comparing strings,
        such as: equals, equalsIgnoreCase, compareTo, hashCode, intern

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for function comparing strings, such as:
///   equals, equalsIgnoreCase, compareTo, hashCode, intern

#include <solvers/refinement/string_constraint_generator.h>

/// add axioms stating that the result is true exactly when the strings
/// represented by the arguments are equal
/// \par parameters: function application with two string arguments
/// \return a expression of Boolean type
exprt string_constraint_generatort::add_axioms_for_equals(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  symbol_exprt eq=fresh_boolean("equal");
  typecast_exprt tc_eq(eq, f.type());

  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=get_string_expr(args(f, 2)[1]);
  typet index_type=s1.length().type();

  // We want to write:
  // eq <=> (s1.length=s2.length  &&forall i<s1.length. s1[i]=s2[i])
  // We add axioms:
  // a1 : eq => s1.length=s2.length
  // a2 : forall i<s1.length. eq => s1[i]=s2[i]
  // a3 : !eq => s1.length!=s2.length
  //       || (witness<s1.length &&s1[witness]!=s2[witness])

  implies_exprt a1(eq, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal", index_type);
  string_constraintt a2(qvar, s1.length(), eq, equal_exprt(s1[qvar], s2[qvar]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_unequal", index_type);
  exprt zero=from_integer(0, index_type);
  and_exprt bound_witness(
    binary_relation_exprt(witness, ID_lt, s1.length()),
    binary_relation_exprt(witness, ID_ge, zero));
  and_exprt witnessing(bound_witness, notequal_exprt(s1[witness], s2[witness]));
  and_exprt diff_length(
    notequal_exprt(s1.length(), s2.length()),
    equal_exprt(witness, from_integer(-1, index_type)));
  implies_exprt a3(not_exprt(eq), or_exprt(diff_length, witnessing));
  axioms.push_back(a3);

  return tc_eq;
}

/// returns an expression which is true when the two given characters are equal
/// when ignoring case for ASCII
/// \par parameters: two character expressions and constant character
///   expressions
/// representing 'a', 'A' and 'Z'
/// \return a expression of Boolean type
exprt string_constraint_generatort::character_equals_ignore_case(
  exprt char1, exprt char2, exprt char_a, exprt char_A, exprt char_Z)
{
  and_exprt is_upper_case_1(
    binary_relation_exprt(char_A, ID_le, char1),
    binary_relation_exprt(char1, ID_le, char_Z));
  and_exprt is_upper_case_2(
    binary_relation_exprt(char_A, ID_le, char2),
    binary_relation_exprt(char2, ID_le, char_Z));

  // Three possibilities:
  // p1 : char1=char2
  // p2 : (is_up1&&'a'-'A'+char1=char2)
  // p3 : (is_up2&&'a'-'A'+char2=char1)
  equal_exprt p1(char1, char2);
  minus_exprt diff=minus_exprt(char_a, char_A);

  // Overflow is not a problem here because is_upper_case conditions
  // ensure that we are within a safe range.
  and_exprt p2(is_upper_case_1,
               equal_exprt(plus_exprt(diff, char1), char2));
  and_exprt p3(is_upper_case_2,
               equal_exprt(plus_exprt(diff, char2), char1));
  return or_exprt(or_exprt(p1, p2), p3);
}

/// add axioms corresponding to the String.equalsIgnoreCase java function
/// \par parameters: function application with two string arguments
/// \return a Boolean expression
exprt string_constraint_generatort::add_axioms_for_equals_ignore_case(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt eq=fresh_boolean("equal_ignore_case");
  typecast_exprt tc_eq(eq, f.type());
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=get_string_expr(args(f, 2)[1]);
  typet char_type=to_refined_string_type(s1.type()).get_char_type();
  exprt char_a=constant_char('a', char_type);
  exprt char_A=constant_char('A', char_type);
  exprt char_Z=constant_char('Z', char_type);
  typet index_type=s1.length().type();

  // We add axioms:
  // a1 : eq => |s1|=|s2|
  // a2 : forall qvar, 0<=qvar<|s1|,
  //  eq => char_equal_ignore_case(s1[qvar],s2[qvar]);
  // a3 : !eq => |s1|!=s2 || (0 <=witness<|s1| &&!char_equal_ignore_case)

  implies_exprt a1(eq, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal_ignore_case", index_type);
  exprt constr2=character_equals_ignore_case(
    s1[qvar], s2[qvar], char_a, char_A, char_Z);
  string_constraintt a2(qvar, s1.length(), eq, constr2);
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index(
    "witness_unequal_ignore_case", index_type);
  exprt zero=from_integer(0, witness.type());
  and_exprt bound_witness(
    binary_relation_exprt(witness, ID_lt, s1.length()),
    binary_relation_exprt(witness, ID_ge, zero));
  exprt witness_eq=character_equals_ignore_case(
    s1[witness], s2[witness], char_a, char_A, char_Z);
  not_exprt witness_diff(witness_eq);
  implies_exprt a3(
    not_exprt(eq),
    or_exprt(
      notequal_exprt(s1.length(), s2.length()),
      and_exprt(bound_witness, witness_diff)));
  axioms.push_back(a3);

  return tc_eq;
}

/// add axioms stating that if two strings are equal then their hash codes are
/// equals
/// \par parameters: function application with a string argument
/// \return a integer expression corresponding to the hash code of the string
exprt string_constraint_generatort::add_axioms_for_hash_code(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  typet return_type=f.type();
  typet index_type=str.length().type();

  auto pair=hash_code_of_string.insert(
    std::make_pair(str, fresh_symbol("hash", return_type)));
  exprt hash=pair.first->second;

  // for each string s. either:
  //   c1: hash(str)=hash(s)
  //   c2: |str|!=|s|
  //   c3: (|str|==|s| && exists i<|s|. s[i]!=str[i])

  // WARNING: the specification may be incomplete
  for(auto it : hash_code_of_string)
  {
    symbol_exprt i=fresh_exist_index("index_hash", index_type);
    equal_exprt c1(it.second, hash);
    not_exprt c2(equal_exprt(it.first.length(), str.length()));
    and_exprt c3(
      equal_exprt(it.first.length(), str.length()),
      and_exprt(
        not_exprt(equal_exprt(str[i], it.first[i])),
        and_exprt(
          str.axiom_for_is_strictly_longer_than(i),
          axiom_for_is_positive_index(i))));
    axioms.push_back(or_exprt(c1, or_exprt(c2, c3)));
  }
  return hash;
}

/// add axioms corresponding to the String.compareTo java function
/// \par parameters: function application with two string arguments
/// \return a integer expression
exprt string_constraint_generatort::add_axioms_for_compare_to(
  const function_application_exprt &f)
{
  string_exprt s1=get_string_expr(args(f, 2)[0]);
  string_exprt s2=get_string_expr(args(f, 2)[1]);
  const typet &return_type=f.type();
  symbol_exprt res=fresh_symbol("compare_to", return_type);
  typet index_type=s1.length().type();

  // In the lexicographic comparison, x is the first point where the two
  // strings differ.
  // We add axioms:
  // a1 : res==0 => |s1|=|s2|
  // a2 : forall i<|s1|. s1[i]==s2[i]
  // a3 : exists x.
  //        res!=0 ==> x > 0
  //        && ((|s1| <= |s2| && x<|s1|) || (|s1| >= |s2| &&x<|s2|)
  //        && res=s1[x]-s2[x] )
  //     || cond2:
  //       (|s1|<|s2| &&x=|s1|) || (|s1| > |s2| &&x=|s2|) &&res=|s1|-|s2|)
  // a4 : forall i'<x. res!=0 => s1[i]=s2[i]

  assert(return_type.id()==ID_signedbv);

  equal_exprt res_null=equal_exprt(res, from_integer(0, return_type));
  implies_exprt a1(res_null, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt i=fresh_univ_index("QA_compare_to", index_type);
  string_constraintt a2(i, s1.length(), res_null, equal_exprt(s1[i], s2[i]));
  axioms.push_back(a2);

  symbol_exprt x=fresh_exist_index("index_compare_to", index_type);
  equal_exprt ret_char_diff(
    res,
    minus_exprt(
      typecast_exprt(s1[x], return_type),
      typecast_exprt(s2[x], return_type)));
  equal_exprt ret_length_diff(
    res,
    minus_exprt(
      typecast_exprt(s1.length(), return_type),
      typecast_exprt(s2.length(), return_type)));
  or_exprt guard1(
    and_exprt(s1.axiom_for_is_shorter_than(s2),
              s1.axiom_for_is_strictly_longer_than(x)),
    and_exprt(s1.axiom_for_is_longer_than(s2),
              s2.axiom_for_is_strictly_longer_than(x)));
  and_exprt cond1(ret_char_diff, guard1);
  or_exprt guard2(
    and_exprt(s2.axiom_for_is_strictly_longer_than(s1),
              s1.axiom_for_has_length(x)),
    and_exprt(s1.axiom_for_is_strictly_longer_than(s2),
              s2.axiom_for_has_length(x)));
  and_exprt cond2(ret_length_diff, guard2);

  implies_exprt a3(
    not_exprt(res_null),
    and_exprt(
      binary_relation_exprt(x, ID_ge, from_integer(0, return_type)),
      or_exprt(cond1, cond2)));
  axioms.push_back(a3);

  symbol_exprt i2=fresh_univ_index("QA_compare_to", index_type);
  string_constraintt a4(
    i2, x, not_exprt(res_null), equal_exprt(s1[i2], s2[i2]));
  axioms.push_back(a4);

  return res;
}

/// add axioms stating that the return value for two equal string should be the
/// same
/// \par parameters: function application with one string argument
/// \return a string expression
symbol_exprt string_constraint_generatort::add_axioms_for_intern(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  // For now we only enforce content equality and not pointer equality
  const typet &return_type=f.type();

  typet index_type=str.length().type();

  auto pair=intern_of_string.insert(
    std::make_pair(str, fresh_symbol("pool", return_type)));
  symbol_exprt intern=pair.first->second;

  // intern(str)=s_0 || s_1 || ...
  // for each string s.
  //    intern(str)=intern(s) || |str|!=|s|
  //    || (|str|==|s| &&exists i<|s|. s[i]!=str[i])

  exprt disj=false_exprt();
  for(auto it : intern_of_string)
    disj=or_exprt(
      disj, equal_exprt(intern, it.second));

  axioms.push_back(disj);


  // WARNING: the specification may be incomplete or incorrect
  for(auto it : intern_of_string)
    if(it.second!=str)
    {
      symbol_exprt i=fresh_exist_index("index_intern", index_type);
      axioms.push_back(
        or_exprt(
          equal_exprt(it.second, intern),
          or_exprt(
            not_exprt(str.axiom_for_has_same_length_as(it.first)),
            and_exprt(
              str.axiom_for_has_same_length_as(it.first),
              and_exprt(
                not_exprt(equal_exprt(str[i], it.first[i])),
                and_exprt(str.axiom_for_is_strictly_longer_than(i),
                          axiom_for_is_positive_index(i)))))));
    }

  return intern;
}
