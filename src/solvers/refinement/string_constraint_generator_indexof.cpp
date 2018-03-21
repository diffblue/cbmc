/*******************************************************************\

Module: Generates string constraints for the family of indexOf and
        lastIndexOf java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of indexOf and lastIndexOf java
///   functions

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>

/// Add axioms stating that the returned value is the index within `haystack`
/// (`str`) of the first occurrence of `needle` (`c`) starting the search at
/// `from_index`, or is `-1` if no such character occurs at or after position
/// `from_index`.
/// \todo Make argument names match whose of add_axioms_for_index_of_string
///
/// These axioms are:
///   1. \f$-1 \le {\tt index} < |{\tt haystack}| \f$
///   2. \f$ \lnot contains \Leftrightarrow {\tt index} = -1 \f$
///   3. \f$ contains \Rightarrow {\tt from\_index} \le {\tt index}
///          \land {\tt haystack}[{\tt index}] = {\tt needle} \f$
///   4. \f$ \forall i \in [{\tt from\_index}, {\tt index}).\ contains
///          \Rightarrow {\tt haystack}[i] \ne {\tt needle} \f$
///   5. \f$ \forall m, n \in [{\tt from\_index}, |{\tt haystack}|)
///          .\ \lnot contains \Rightarrow {\tt haystack}[m] \ne {\tt needle}
///      \f$
/// \param str: an array of characters expression
/// \param c: a character expression
/// \param from_index: an integer expression
/// \return integer expression `index`
exprt string_constraint_generatort::add_axioms_for_index_of(
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index)
{
  const typet &index_type=str.length().type();
  symbol_exprt index=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_in_index_of");

  exprt minus1=from_integer(-1, index_type);
  and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_lt, str.length()));
  lemmas.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  lemmas.push_back(a2);

  implies_exprt a3(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, index),
      equal_exprt(str[index], c)));
  lemmas.push_back(a3);

  const auto zero = from_integer(0, index_type);
  const if_exprt lower_bound(
    binary_relation_exprt(from_index, ID_le, zero), zero, from_index);

  symbol_exprt n=fresh_univ_index("QA_index_of", index_type);
  string_constraintt a4;
  a4.univ_var = n;
  a4.lower_bound = lower_bound;
  a4.upper_bound = index;
  a4.body = implies_exprt(contains, not_exprt(equal_exprt(str[n], c)));
  constraints.push_back(a4);

  symbol_exprt m=fresh_univ_index("QA_index_of", index_type);
  string_constraintt a5;
  a5.univ_var = m;
  a5.lower_bound = lower_bound;
  a5.upper_bound = str.length();
  a5.body = implies_exprt(not_exprt(contains), notequal_exprt(str[m], c));
  constraints.push_back(a5);

  return index;
}

/// Add axioms stating that the returned value `index` is the index within
/// `haystack` of the first occurrence of `needle` starting the search at
/// `from_index`, or `-1` if needle does not occur at or after position
/// `from_index`.
/// If needle is an empty string then the result is `from_index`.
///
/// These axioms are:
///   1. \f$ contains \Rightarrow {\tt from\_index} \le \tt{index}
///          \le |{\tt haystack}|-|{\tt needle} | \f$
///   2. \f$ \lnot contains \Leftrightarrow {\tt index} = -1 \f$
///   3. \f$ \forall n \in [0,|{\tt needle}|).\ contains
///          \Rightarrow {\tt haystack}[n + {\tt index}] = {\tt needle}[n] \f$
///   4. \f$ \forall n \in [{\tt from\_index}, {\tt index}).\ contains
///          \Rightarrow (\exists m \in [0,|{\tt needle}|).\ {\tt haystack}[m+n]
///          \ne {\tt needle}[m]]) \f$
///   5. \f$ \forall n \in [{\tt from\_index},|{\tt haystack}|-|{\tt needle}|]
///          .\ \lnot contains \Rightarrow (\exists m \in [0,|{\tt needle}|)
///          .\ {\tt haystack}[m+n] \ne {\tt needle}[m]) \f$
///   6. \f$ |{\tt needle}| = 0 \Rightarrow \tt{index} = from_index \f$
/// \param haystack: an array of character expression
/// \param needle: an array of character expression
/// \param from_index: an integer expression
/// \return integer expression `index` representing the first index of `needle`
///   in `haystack`
exprt string_constraint_generatort::add_axioms_for_index_of_string(
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index)
{
  const typet &index_type=haystack.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  implies_exprt a1(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, offset),
      binary_relation_exprt(
        offset, ID_le, minus_exprt(haystack.length(), needle.length()))));
  lemmas.push_back(a1);

  equal_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  lemmas.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  string_constraintt a3;
  a3.univ_var = qvar;
  a3.upper_bound = needle.length();
  a3.body = implies_exprt(
    contains, equal_exprt(haystack[plus_exprt(qvar, offset)], needle[qvar]));
  constraints.push_back(a3);

  // string_not contains_constraintt are formulas of the form:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]
  string_not_contains_constraintt a4(
    from_index,
    offset,
    contains,
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle);
  not_contains_constraints.push_back(a4);

  string_not_contains_constraintt a5(
    from_index,
    plus_exprt( // Add 1 for inclusive upper bound.
      minus_exprt(haystack.length(), needle.length()),
      from_integer(1, index_type)),
    not_exprt(contains),
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle);
  not_contains_constraints.push_back(a5);

  const implies_exprt a6(
    equal_exprt(needle.length(), from_integer(0, index_type)),
    equal_exprt(offset, from_index));
  lemmas.push_back(a6);

  return offset;
}

/// Add axioms stating that the returned value is the index within haystack of
/// the last occurrence of needle starting the search backward at from_index (ie
/// the index is smaller or equal to from_index), or -1 if needle does not occur
/// before from_index.
/// If `needle` is the empty string, the result is `from_index`.
///
/// These axioms are:
///   1. \f$ contains \Rightarrow -1 \le {\tt index}
///          \land {\tt index} \le {\tt from\_index}
///          \land {\tt index} \le |{\tt haystack}| - |{\tt needle}| \f$
///   2. \f$ \lnot contains \Leftrightarrow {\tt index}= -1 \f$
///   3. \f$ \forall n \in [0, |{\tt needle}|).\ contains
///          \Rightarrow {\tt haystack}[n+{\tt index}] = {\tt needle}[n] \f$
///   4. \f$ \forall n \in [{\tt index}+1,
///                         min({\tt from\_index},
///                             |{\tt haystack}| - |{\tt needle}|)]
///          .\ contains \Rightarrow
///          (\exists m \in [0,|{\tt needle}|)
///          .\ {\tt haystack}[m+n] \ne {\tt needle}[m]]) \f$
///   5. \f$ \forall n \in
///          [0, min({\tt from\_index}, |{\tt haystack}| - |{\tt needle}|)]
///          .\ \lnot contains \Rightarrow
///          (\exists m \in [0,|{\tt needle}|)
///          .\ {\tt haystack}[m+n] \ne {\tt needle}[m]) \f$
///   6. \f$ |{\tt needle}| = 0 \Rightarrow index = from_index \f$
/// \param haystack: an array of characters expression
/// \param needle: an array of characters expression
/// \param from_index: integer expression
/// \return integer expression `index` representing the last index of `needle`
///         in `haystack` before or at `from_index`, or -1 if there is none
exprt string_constraint_generatort::add_axioms_for_last_index_of_string(
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index)
{
  const typet &index_type=haystack.length().type();
  symbol_exprt offset=fresh_exist_index("index_of", index_type);
  symbol_exprt contains=fresh_boolean("contains_substring");

  implies_exprt a1(
    contains,
    and_exprt(
      binary_relation_exprt(from_integer(-1, index_type), ID_le, offset),
      binary_relation_exprt(
        offset, ID_le, minus_exprt(haystack.length(), needle.length())),
      binary_relation_exprt(offset, ID_le, from_index)));
  lemmas.push_back(a1);

  equal_exprt a2(
    not_exprt(contains),
    equal_exprt(offset, from_integer(-1, index_type)));
  lemmas.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string", index_type);
  equal_exprt constr3(haystack[plus_exprt(qvar, offset)], needle[qvar]);
  string_constraintt a3;
  a3.univ_var = qvar;
  a3.upper_bound = needle.length();
  a3.body = implies_exprt(contains, constr3);
  constraints.push_back(a3);

  // end_index is min(from_index, |str| - |substring|)
  minus_exprt length_diff(haystack.length(), needle.length());
  if_exprt end_index(
    binary_relation_exprt(from_index, ID_le, length_diff),
    from_index,
    length_diff);

  string_not_contains_constraintt a4(
    plus_exprt(offset, from_integer(1, index_type)),
    plus_exprt(end_index, from_integer(1, index_type)),
    contains,
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle);
  not_contains_constraints.push_back(a4);

  string_not_contains_constraintt a5(
    from_integer(0, index_type),
    plus_exprt(end_index, from_integer(1, index_type)),
    not_exprt(contains),
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle);
  not_contains_constraints.push_back(a5);

  const implies_exprt a6(
    equal_exprt(needle.length(), from_integer(0, index_type)),
    equal_exprt(offset, from_index));
  lemmas.push_back(a6);

  return offset;
}

/// Index of the first occurence of a target inside the string
///
/// If the target is a character:
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_index_of(const array_string_exprt&,const exprt&,const exprt&)
/// \link
/// add_axioms_for_index_of(const array_string_exprt&,const exprt&,const exprt&)
/// (More...) \endlink
///
/// If the target is a refined_string:
/// \copybrief string_constraint_generatort::add_axioms_for_index_of_string
/// \link string_constraint_generatort::add_axioms_for_index_of_string (More...)
/// \endlink
/// \warning slow for string targets
/// \param f: function application with arguments refined_string `haystack`,
///           refined_string or character `needle`, and optional integer
///           `from_index` with default value `0`
/// \return integer expression
exprt string_constraint_generatort::add_axioms_for_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt str = get_string_expr(args[0]);
  const exprt &c=args[1];
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  PRECONDITION(f.type() == index_type);
  const exprt from_index =
    args.size() == 2 ? from_integer(0, index_type) : args[2];

  if(c.type().id()==ID_unsignedbv || c.type().id()==ID_signedbv)
  {
    return add_axioms_for_index_of(
      str, typecast_exprt(c, char_type), from_index);
  }
  else
  {
    INVARIANT(
      is_refined_string_type(c.type()),
      string_refinement_invariantt("c can only be a (un)signedbv or a refined "
        "string and the (un)signedbv case is already handled"));
    array_string_exprt sub = get_string_expr(c);
    return add_axioms_for_index_of_string(str, sub, from_index);
  }
}

/// Add axioms stating that the returned value is the index within `haystack`
/// (`str`) of the last occurrence of `needle` (`c`) starting the search
/// backward at `from_index`, or `-1` if no such character occurs at or before
/// position `from_index`.
/// \todo Change argument names to match add_axioms_for_last_index_of_string
///
/// These axioms are :
///   1. \f$ -1 \le {\tt index} \le {\tt from\_index}
///          \land {\tt index} < |{\tt haystack}| \f$
///   2. \f$ {\tt index} = -1 \Leftrightarrow \lnot contains\f$
///   3. \f$ contains \Rightarrow
///          {\tt haystack}[{\tt index}] = {\tt needle} )\f$
///   4. \f$ \forall n \in [{\tt index} +1,
///                         min({\tt from\_index}+1, |{\tt haystack}|))
///          .\ contains \Rightarrow {\tt haystack}[n] \ne {\tt needle} \f$
///   5. \f$ \forall m \in [0,
///          min({\tt from\_index}+1, |{\tt haystack}|))
///          .\ \lnot contains \Rightarrow {\tt haystack}[m] \ne {\tt needle}\f$
/// \param str: an array of characters expression
/// \param c: a character expression
/// \param from_index: an integer expression
/// \return integer expression `index` representing the last index of `needle`
///         in `haystack` before or at `from_index`, or `-1` if there is none
exprt string_constraint_generatort::add_axioms_for_last_index_of(
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index)
{
  const typet &index_type = str.length().type();
  const symbol_exprt index = fresh_exist_index("last_index_of", index_type);
  const symbol_exprt contains = fresh_boolean("contains_in_last_index_of");

  const exprt minus1 = from_integer(-1, index_type);
  const and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_le, from_index),
    binary_relation_exprt(index, ID_lt, str.length()));
  lemmas.push_back(a1);

  const notequal_exprt a2(contains, equal_exprt(index, minus1));
  lemmas.push_back(a2);

  const implies_exprt a3(contains, equal_exprt(str[index], c));
  lemmas.push_back(a3);

  const exprt index1 = from_integer(1, index_type);
  const exprt from_index_plus_one =
    plus_exprt_with_overflow_check(from_index, index1);
  const if_exprt end_index(
    binary_relation_exprt(from_index_plus_one, ID_le, str.length()),
    from_index_plus_one,
    str.length());

  const symbol_exprt n = fresh_univ_index("QA_last_index_of1", index_type);
  string_constraintt a4;
  a4.univ_var = n;
  a4.lower_bound = plus_exprt(index, index1);
  a4.upper_bound = end_index;
  a4.body = implies_exprt(contains, notequal_exprt(str[n], c));
  constraints.push_back(a4);

  const symbol_exprt m = fresh_univ_index("QA_last_index_of2", index_type);
  string_constraintt a5;
  a5.univ_var = m;
  a5.upper_bound = end_index;
  a5.body = implies_exprt(not_exprt(contains), notequal_exprt(str[m], c));
  constraints.push_back(a5);

  return index;
}

/// Index of the last occurence of a target inside the string
///
/// If the target is a character:
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_last_index_of(const array_string_exprt&,const exprt&,const exprt&)
// NOLINTNEXTLINE
/// \link add_axioms_for_last_index_of(const array_string_exprt&,const exprt&,const exprt&)
///   (More...) \endlink
///
/// If the target is a refined_string:
/// \copybrief string_constraint_generatort::add_axioms_for_last_index_of_string
/// \link string_constraint_generatort::add_axioms_for_last_index_of_string
///   (More...) \endlink
/// \warning slow for string targets
/// \param f: function application with arguments refined_string `haystack`,
///           refined_string or character `needle`, and optional integer
///           `from_index` with default value `|haystack|-1`
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt str = get_string_expr(args[0]);
  const exprt c = args[1];
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  PRECONDITION(f.type() == index_type);

  const exprt from_index = args.size() == 2 ? str.length() : args[2];

  if(c.type().id()==ID_unsignedbv || c.type().id()==ID_signedbv)
  {
    return add_axioms_for_last_index_of(
      str, typecast_exprt(c, char_type), from_index);
  }
  else
  {
    const array_string_exprt sub = get_string_expr(c);
    return add_axioms_for_last_index_of_string(str, sub, from_index);
  }
}
