/*******************************************************************\

Module: Generates string constraints for function comparing strings,
        such as: equals, equalsIgnoreCase, compareTo, hashCode, intern

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_equals

  Inputs: function application with two string arguments

 Outputs: a expression of Boolean type

 Purpose: add axioms stating that the result is true exactly when the strings
          represented by the arguments are equal

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_equals(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  symbol_exprt eq=fresh_boolean("equal");
  typecast_exprt tc_eq(eq, f.type());

  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);

  // We want to write:
  // eq <=> (s1.length=s2.length  &&forall i<s1.length. s1[i]=s2[i])
  // We add axioms:
  // a1 : eq => s1.length=s2.length
  // a2 : forall i<s1.length. eq => s1[i]=s2[i]
  // a3 : !eq => s1.length!=s2.length
  //       || (witness<s1.length &&s1[witness]!=s2[witness])

  implies_exprt a1(eq, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal");
  string_constraintt a2(qvar, s1.length(), eq, equal_exprt(s1[qvar], s2[qvar]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_unequal");
  exprt zero=from_integer(0, get_index_type());
  and_exprt bound_witness(
    binary_relation_exprt(witness, ID_lt, s1.length()),
    binary_relation_exprt(witness, ID_ge, zero));
  and_exprt witnessing(bound_witness, notequal_exprt(s1[witness], s2[witness]));
  implies_exprt a3(
    not_exprt(eq),
    or_exprt(notequal_exprt(s1.length(), s2.length()), witnessing));
  axioms.push_back(a3);

  return tc_eq;
}

/*******************************************************************\

Function: string_constraint_generatort::character_equals_ignore_case

  Inputs: two character expressions and constant character expressions
          representing 'a', 'A' and 'Z'

 Outputs: a expression of Boolean type

 Purpose: returns an expression which is true when the two given
          characters are equal when ignoring case for ASCII

\*******************************************************************/

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
  and_exprt p2(is_upper_case_1, equal_exprt(plus_exprt(diff, char1), char2));
  and_exprt p3(is_upper_case_2, equal_exprt(plus_exprt(diff, char2), char1));
  return or_exprt(or_exprt(p1, p2), p3);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_equals_ignore_case

  Inputs: function application with two string arguments

 Outputs: a Boolean expression

 Purpose: add axioms corresponding to the String.equalsIgnoreCase java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_equals_ignore_case(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt eq=fresh_boolean("equal_ignore_case");
  typecast_exprt tc_eq(eq, f.type());
  exprt char_a=constant_char('a');
  exprt char_A=constant_char('A');
  exprt char_Z=constant_char('Z');
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);

  // We add axioms:
  // a1 : eq => |s1|=|s2|
  // a2 : forall qvar, 0<=qvar<|s1|,
  //  eq => char_equal_ignore_case(s1[qvar],s2[qvar]);
  // a3 : !eq => |s1|!=s2 || (0 <=witness<|s1| &&!char_equal_ignore_case)

  implies_exprt a1(eq, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal_ignore_case");
  exprt constr2=character_equals_ignore_case(
    s1[qvar], s2[qvar], char_a, char_A, char_Z);
  string_constraintt a2(qvar, s1.length(), eq, constr2);
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_unequal_ignore_case");
  exprt zero=from_integer(0, get_index_type());
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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_hash_code

  Inputs: function application with a string argument

 Outputs: a integer expression corresponding to the hash code of the string

 Purpose: add axioms stating that if two strings are equal then their hash
          codes are equals

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_hash_code(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  typet return_type=f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(hash.find(it->second)==hash.end())
      hash[it->second]=string_exprt::fresh_symbol("hash", return_type);

  // for each string s. either:
  //   c1: hash(str)=hash(s)
  //   c2: |str|!=|s|
  //   c3: (|str|==|s| &&exists i<|s|. s[i]!=str[i])

  // WARNING: the specification may be incomplete
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
  {
    symbol_exprt i=fresh_exist_index("index_hash");
    equal_exprt c1(hash[it->second], hash[str]);
    not_exprt c2(equal_exprt(it->second.length(), str.length()));
    and_exprt c3(
      equal_exprt(it->second.length(), str.length()),
      and_exprt(
        not_exprt(equal_exprt(str[i], it->second[i])),
        and_exprt(
          str.axiom_for_is_strictly_longer_than(i),
          axiom_for_is_positive_index(i))));
    axioms.push_back(or_exprt(c1, or_exprt(c2, c3)));
  }
  return hash[str];
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_compare_to

  Inputs: function application with two string arguments

 Outputs: a integer expression

 Purpose: add axioms corresponding to the String.compareTo java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_compare_to(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);
  const typet &return_type=f.type();
  symbol_exprt res=string_exprt::fresh_symbol("compare_to", return_type);

  // In the lexicographic comparison, x is the first point where the two
  // strings differ.
  // We add axioms:
  // a1 : res==0 => |s1|=|s2|
  // a2 : forall i<|s1|. s1[i]==s2[i]
  // a3 : exists x.
  // res!=0 ==> x> 0 &&
  //   ((|s1| <= |s2| &&x<|s1|) || (|s1| >= |s2| &&x<|s2|)
  //   &&res=s1[x]-s2[x] )
  // || cond2:
  //   (|s1|<|s2| &&x=|s1|) || (|s1| > |s2| &&x=|s2|) &&res=|s1|-|s2|)
  // a4 : forall i<x. res!=0 => s1[i]=s2[i]

  assert(return_type.id()==ID_signedbv);

  equal_exprt res_null=equal_exprt(res, from_integer(0, return_type));
  implies_exprt a1(res_null, s1.axiom_for_has_same_length_as(s2));
  axioms.push_back(a1);

  symbol_exprt i=fresh_univ_index("QA_compare_to");
  string_constraintt a2(i, s1.length(), res_null, equal_exprt(s1[i], s2[i]));
  axioms.push_back(a2);

  symbol_exprt x=fresh_exist_index("index_compare_to");
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

  string_constraintt a4(i, x, not_exprt(res_null), equal_exprt(s1[i], s2[i]));
  axioms.push_back(a4);

  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_intern

  Inputs: function application with one string argument

 Outputs: a string expression

 Purpose: add axioms stating that the return value for two equal string
          should be the same

\*******************************************************************/

symbol_exprt string_constraint_generatort::add_axioms_for_intern(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  const typet &return_type=f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(pool.find(it->second)==pool.end())
      pool[it->second]=string_exprt::fresh_symbol("pool", return_type);

  // intern(str)=s_0 || s_1 || ...
  // for each string s.
  //    intern(str)=intern(s) || |str|!=|s|
  //    || (|str|==|s| &&exists i<|s|. s[i]!=str[i])

  // symbol_exprt intern=string_exprt::fresh_symbol("intern",return_type);

  exprt disj=false_exprt();
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    disj=or_exprt(
      disj, equal_exprt(pool[str], symbol_exprt(it->first, return_type)));

  axioms.push_back(disj);


  // WARNING: the specification may be incomplete or incorrect
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(it->second!=str)
    {
      symbol_exprt i=fresh_exist_index("index_intern");
      axioms.push_back(
        or_exprt(
          equal_exprt(pool[it->second], pool[str]),
          or_exprt(
            not_exprt(str.axiom_for_has_same_length_as(it->second)),
            and_exprt(
              str.axiom_for_has_same_length_as(it->second),
              and_exprt(
                not_exprt(equal_exprt(str[i], it->second[i])),
                and_exprt(str.axiom_for_is_strictly_longer_than(i),
                          axiom_for_is_positive_index(i)))))));
    }

  return pool[str];
}
