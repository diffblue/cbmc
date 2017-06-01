/*******************************************************************\

Module: Generates string constraints for string functions that return
        Boolean values

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_is_prefix

  Inputs: a prefix string, a string and an integer offset

 Outputs: a Boolean expression

 Purpose: add axioms stating that the returned expression is true exactly
          when the first string is a prefix of the second one, starting at
          position offset

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_is_prefix(
  const string_exprt &prefix, const string_exprt &str, const exprt &offset)
{
  symbol_exprt isprefix=fresh_boolean("isprefix");
  const typet &index_type=str.length().type();

  // We add axioms:
  // a1 : isprefix => |str| >= |prefix|+offset
  // a2 : forall 0<=qvar<|prefix|. isprefix => s0[witness+offset]=s2[witness]
  // a3 : !isprefix =>
  //        |str|<|prefix|+offset ||
  //        (0<=witness<|prefix| && str[witness+offset]!=prefix[witness])

  implies_exprt a1(
    isprefix,
    str.axiom_for_is_longer_than(plus_exprt_with_overflow_check(
      prefix.length(), offset)));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_isprefix", index_type);
  string_constraintt a2(
    qvar,
    prefix.length(),
    isprefix,
    equal_exprt(str[plus_exprt_with_overflow_check(qvar, offset)],
                prefix[qvar]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_isprefix", index_type);
  and_exprt witness_diff(
    axiom_for_is_positive_index(witness),
    and_exprt(
      prefix.axiom_for_is_strictly_longer_than(witness),
      notequal_exprt(str[plus_exprt_with_overflow_check(witness, offset)],
                     prefix[witness])));
  or_exprt s0_notpref_s1(
    not_exprt(
      str.axiom_for_is_longer_than(
        plus_exprt_with_overflow_check(prefix.length(), offset))),
    witness_diff);

  implies_exprt a3(not_exprt(isprefix), s0_notpref_s1);
  axioms.push_back(a3);
  return isprefix;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_is_prefix

  Inputs: a function application with 2 or 3 arguments and a Boolean telling
          whether the prefix is the second argument (when swap_arguments is
          true) or the first argument

 Outputs: a Boolean expression

 Purpose: add axioms corresponding to the String.isPrefix java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_is_prefix(
  const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  string_exprt s0=get_string_expr(args[swap_arguments?1:0]);
  string_exprt s1=get_string_expr(args[swap_arguments?0:1]);
  exprt offset;
  if(args.size()==2)
    offset=from_integer(0, s0.length().type());
  else if(args.size()==3)
    offset=args[2];
  return typecast_exprt(add_axioms_for_is_prefix(s0, s1, offset), f.type());
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_is_empty

  Inputs: function application with a string argument

 Outputs: a Boolean expression

 Purpose: add axioms stating that the returned value is true exactly when
          the argument string is empty

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_is_empty(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  // We add axioms:
  // a1 : is_empty => |s0| = 0
  // a2 : s0 => is_empty

  symbol_exprt is_empty=fresh_boolean("is_empty");
  string_exprt s0=get_string_expr(args(f, 1)[0]);
  axioms.push_back(implies_exprt(is_empty, s0.axiom_for_has_length(0)));
  axioms.push_back(implies_exprt(s0.axiom_for_has_length(0), is_empty));
  return typecast_exprt(is_empty, f.type());
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_is_suffix

  Inputs: a function application with 2 or 3 arguments and a Boolean telling
          whether the suffix is the second argument (when swap_arguments is
          true) or the first argument

 Outputs: a Boolean expression

 Purpose: add axioms corresponding to the String.isSuffix java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_is_suffix(
  const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2); // bad args to string issuffix?
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt issuffix=fresh_boolean("issuffix");
  typecast_exprt tc_issuffix(issuffix, f.type());
  string_exprt s0=get_string_expr(args[swap_arguments?1:0]);
  string_exprt s1=get_string_expr(args[swap_arguments?0:1]);
  const typet &index_type=s0.length().type();

  // We add axioms:
  // a1 : issufix => s0.length >= s1.length
  // a2 : forall witness<s1.length.
  //     issufix => s1[witness]=s0[witness + s0.length-s1.length]
  // a3 : !issuffix =>
  //   (s1.length > s0.length && witness=-1)
  //     || (s1.length > witness>=0
  //       &&s1[witness]!=s0[witness + s0.length-s1.length]

  implies_exprt a1(issuffix, s1.axiom_for_is_longer_than(s0));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_suffix", index_type);
  exprt qvar_shifted=plus_exprt(
    qvar, minus_exprt(s1.length(), s0.length()));
  string_constraintt a2(
    qvar, s0.length(), issuffix, equal_exprt(s0[qvar], s1[qvar_shifted]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_suffix", index_type);
  exprt shifted=plus_exprt(
    witness, minus_exprt(s1.length(), s0.length()));
  or_exprt constr3(
    and_exprt(s0.axiom_for_is_strictly_longer_than(s1),
              equal_exprt(witness, from_integer(-1, index_type))),
    and_exprt(
      notequal_exprt(s0[witness], s1[shifted]),
      and_exprt(
        s0.axiom_for_is_strictly_longer_than(witness),
        axiom_for_is_positive_index(witness))));
  implies_exprt a3(not_exprt(issuffix), constr3);

  axioms.push_back(a3);
  return tc_issuffix;
}

/*******************************************************************\

Function: string_constraint_generatort::is_constant_string

  Inputs:
    expr - a string expression

 Outputs: a Boolean

 Purpose: tells whether the given string is a constant

\*******************************************************************/

bool string_constraint_generatort::is_constant_string(
  const string_exprt &expr) const
{
  if(expr.id()!=ID_struct ||
     expr.operands().size()!=2 ||
     expr.length().id()!=ID_constant ||
     expr.content().id()!=ID_array)
    return false;
  for(const auto &element : expr.content().operands())
  {
    if(element.id()!=ID_constant)
      return false;
  }
  return true;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_contains

  Inputs: function application with two string arguments

 Outputs: a Boolean expression

 Purpose: add axioms corresponding to the String.contains java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_contains(
  const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  string_exprt s0=get_string_expr(args(f, 2)[0]);
  string_exprt s1=get_string_expr(args(f, 2)[1]);
  bool constant=is_constant_string(s1);

  symbol_exprt contains=fresh_boolean("contains");
  const refined_string_typet ref_type=to_refined_string_type(s0.type());
  const typet &index_type=ref_type.get_index_type();

  // We add axioms:
  // a1 : contains ==> |s0| >= |s1|
  // a2 : 0 <= startpos <= |s0|-|s1|
  // a3 : forall qvar < |s1|. contains ==> s1[qvar] = s0[startpos + qvar]
  // a4 : !contains ==> |s1| > |s0| ||
  //      (forall startpos <= |s0| - |s1|.
  //         exists witness < |s1|. s1[witness] != s0[witness + startpos])

  implies_exprt a1(contains, s0.axiom_for_is_longer_than(s1));
  axioms.push_back(a1);

  symbol_exprt startpos=fresh_exist_index("startpos_contains", index_type);
  minus_exprt length_diff(s0.length(), s1.length());
  and_exprt bounds(
    axiom_for_is_positive_index(startpos),
    binary_relation_exprt(startpos, ID_le, length_diff));
  implies_exprt a2(contains, bounds);
  axioms.push_back(a2);

  if(constant)
  {
    // If the string is constant, we can use a more efficient axiom for a3:
    // contains ==> AND_{i < |s1|} s1[i] = s0[startpos + i]
    mp_integer s1_length;
    assert(!to_integer(s1.length(), s1_length));
    exprt::operandst conjuncts;
    for(mp_integer i=0; i<s1_length; ++i)
    {
      exprt expr_i=from_integer(i, index_type);
      plus_exprt shifted_i(expr_i, startpos);
      conjuncts.push_back(equal_exprt(s1[expr_i], s0[shifted_i]));
    }
    implies_exprt a3(contains, conjunction(conjuncts));
    axioms.push_back(a3);

    // The a4 constraint for constant strings translates to:
    // !contains ==> |s1| > |s0| ||
    //               (forall qvar <= |s0| - |s1|.
    //                 !(AND_{i < |s1|} s1[i] == s0[i + qvar])
    //
    // which we implement as:
    // forall qvar <= |s0| - |s1|.  (!contains && |s0| >= |s1|)
    //     ==> !(AND_{i < |s1|} (s1[i] == s0[qvar+i]))
    symbol_exprt qvar=fresh_univ_index("QA_contains_constant", index_type);
    exprt::operandst conjuncts1;
    for(mp_integer i=0; i<s1_length; ++i)
    {
      exprt expr_i=from_integer(i, index_type);
      plus_exprt shifted_i(expr_i, qvar);
      conjuncts1.push_back(equal_exprt(s1[expr_i], s0[shifted_i]));
    }

    string_constraintt a4(
      qvar,
      plus_exprt(from_integer(1, index_type), length_diff),
      and_exprt(not_exprt(contains), s0.axiom_for_is_longer_than(s1)),
      not_exprt(conjunction(conjuncts1)));
    axioms.push_back(a4);
  }
  else
  {
    symbol_exprt qvar=fresh_univ_index("QA_contains", index_type);
    exprt qvar_shifted=plus_exprt(qvar, startpos);
    string_constraintt a3(
      qvar, s1.length(), contains, equal_exprt(s1[qvar], s0[qvar_shifted]));
    axioms.push_back(a3);

    // We rewrite axiom a4 as:
    // forall startpos <= |s0|-|s1|.  (!contains && |s0| >= |s1|)
    //     ==> exists witness < |s1|. s1[witness] != s0[startpos+witness]
    string_not_contains_constraintt a4(
      from_integer(0, index_type),
      plus_exprt(from_integer(1, index_type), length_diff),
      and_exprt(not_exprt(contains), s0.axiom_for_is_longer_than(s1)),
      from_integer(0, index_type), s1.length(), s0, s1);
    axioms.push_back(a4);
  }
  return typecast_exprt(contains, f.type());
}
