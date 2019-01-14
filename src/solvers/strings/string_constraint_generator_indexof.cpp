/*******************************************************************\

Module: Generates string constraints for the family of indexOf and
        lastIndexOf java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of indexOf and lastIndexOf java
///   functions

#include "string_constraint_generator.h"
#include "string_refinement_invariant.h"

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
/// \param fresh_symbol: generator of fresh symbols
/// \param str: an array of characters expression
/// \param c: a character expression
/// \param from_index: an integer expression
/// \return integer expression `index`
std::pair<exprt, string_constraintst> add_axioms_for_index_of(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index)
{
  string_constraintst constraints;
  const typet &index_type = str.length().type();
  symbol_exprt index = fresh_symbol("index_of", index_type);
  symbol_exprt contains = fresh_symbol("contains_in_index_of");

  exprt minus1 = from_integer(-1, index_type);
  and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_lt, str.length()));
  constraints.existential.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  constraints.existential.push_back(a2);

  implies_exprt a3(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, index),
      equal_exprt(str[index], c)));
  constraints.existential.push_back(a3);

  const exprt lower_bound(zero_if_negative(from_index));

  symbol_exprt n = fresh_symbol("QA_index_of", index_type);
  string_constraintt a4(
    n,
    lower_bound,
    zero_if_negative(index),
    implies_exprt(contains, notequal_exprt(str[n], c)));
  constraints.universal.push_back(a4);

  symbol_exprt m = fresh_symbol("QA_index_of", index_type);
  string_constraintt a5(
    m,
    lower_bound,
    zero_if_negative(str.length()),
    implies_exprt(not_exprt(contains), not_exprt(equal_exprt(str[m], c))));
  constraints.universal.push_back(a5);

  return {index, std::move(constraints)};
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
/// \param fresh_symbol: generator of fresh symbols
/// \param haystack: an array of character expression
/// \param needle: an array of character expression
/// \param from_index: an integer expression
/// \return integer expression `index` representing the first index of `needle`
///   in `haystack`
std::pair<exprt, string_constraintst> add_axioms_for_index_of_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index)
{
  string_constraintst constraints;
  const typet &index_type = haystack.length().type();
  symbol_exprt offset = fresh_symbol("index_of", index_type);
  symbol_exprt contains = fresh_symbol("contains_substring");

  implies_exprt a1(
    contains,
    and_exprt(
      binary_relation_exprt(from_index, ID_le, offset),
      binary_relation_exprt(
        offset, ID_le, minus_exprt(haystack.length(), needle.length()))));
  constraints.existential.push_back(a1);

  equal_exprt a2(
    not_exprt(contains), equal_exprt(offset, from_integer(-1, index_type)));
  constraints.existential.push_back(a2);

  symbol_exprt qvar = fresh_symbol("QA_index_of_string", index_type);
  string_constraintt a3(
    qvar,
    zero_if_negative(needle.length()),
    implies_exprt(
      contains, equal_exprt(haystack[plus_exprt(qvar, offset)], needle[qvar])));
  constraints.universal.push_back(a3);

  // string_not contains_constraintt are formulas of the form:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]
  const string_not_contains_constraintt a4 = {from_index,
                                              offset,
                                              contains,
                                              from_integer(0, index_type),
                                              needle.length(),
                                              haystack,
                                              needle};
  constraints.not_contains.push_back(a4);

  const string_not_contains_constraintt a5 = {
    from_index,
    plus_exprt( // Add 1 for inclusive upper bound.
      minus_exprt(haystack.length(), needle.length()),
      from_integer(1, index_type)),
    not_exprt(contains),
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle};
  constraints.not_contains.push_back(a5);

  const implies_exprt a6(
    equal_exprt(needle.length(), from_integer(0, index_type)),
    equal_exprt(offset, from_index));
  constraints.existential.push_back(a6);

  return {offset, std::move(constraints)};
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
/// \param fresh_symbol: generator of fresh symbols
/// \param haystack: an array of characters expression
/// \param needle: an array of characters expression
/// \param from_index: integer expression
/// \return integer expression `index` representing the last index of `needle`
///         in `haystack` before or at `from_index`, or -1 if there is none
std::pair<exprt, string_constraintst> add_axioms_for_last_index_of_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index)
{
  string_constraintst constraints;
  const typet &index_type = haystack.length().type();
  symbol_exprt offset = fresh_symbol("index_of", index_type);
  symbol_exprt contains = fresh_symbol("contains_substring");

  implies_exprt a1(
    contains,
    and_exprt(
      binary_relation_exprt(from_integer(-1, index_type), ID_le, offset),
      binary_relation_exprt(
        offset, ID_le, minus_exprt(haystack.length(), needle.length())),
      binary_relation_exprt(offset, ID_le, from_index)));
  constraints.existential.push_back(a1);

  equal_exprt a2(
    not_exprt(contains), equal_exprt(offset, from_integer(-1, index_type)));
  constraints.existential.push_back(a2);

  symbol_exprt qvar = fresh_symbol("QA_index_of_string", index_type);
  equal_exprt constr3(haystack[plus_exprt(qvar, offset)], needle[qvar]);
  const string_constraintt a3(
    qvar, zero_if_negative(needle.length()), implies_exprt(contains, constr3));
  constraints.universal.push_back(a3);

  // end_index is min(from_index, |str| - |substring|)
  minus_exprt length_diff(haystack.length(), needle.length());
  if_exprt end_index(
    binary_relation_exprt(from_index, ID_le, length_diff),
    from_index,
    length_diff);

  const string_not_contains_constraintt a4 = {
    plus_exprt(offset, from_integer(1, index_type)),
    plus_exprt(end_index, from_integer(1, index_type)),
    contains,
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle};
  constraints.not_contains.push_back(a4);

  string_not_contains_constraintt a5 = {
    from_integer(0, index_type),
    plus_exprt(end_index, from_integer(1, index_type)),
    not_exprt(contains),
    from_integer(0, index_type),
    needle.length(),
    haystack,
    needle};
  constraints.not_contains.push_back(a5);

  const implies_exprt a6(
    equal_exprt(needle.length(), from_integer(0, index_type)),
    equal_exprt(offset, from_index));
  constraints.existential.push_back(a6);

  return {offset, std::move(constraints)};
}

/// Index of the first occurence of a target inside the string
///
/// If the target is a character:
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_index_of(symbol_generatort &fresh_symbol, const array_string_exprt&,const exprt&,const exprt&)
// NOLINTNEXTLINE
/// \link add_axioms_for_index_of(symbol_generatort &fresh_symbol, const array_string_exprt&,const exprt&,const exprt&)
/// (More...) \endlink
///
/// If the target is a refined_string:
/// \copybrief add_axioms_for_index_of_string
/// \link add_axioms_for_index_of_string (More...)
/// \endlink
/// \warning slow for string targets
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `haystack`,
///   refined_string or character `needle`, and optional integer `from_index`
///   with default value `0`
/// \param array_pool: pool of arrays representing strings
/// \return integer expression
std::pair<exprt, string_constraintst> add_axioms_for_index_of(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args = f.arguments();
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt str = get_string_expr(array_pool, args[0]);
  const exprt &c = args[1];
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  PRECONDITION(f.type() == index_type);
  const exprt from_index =
    args.size() == 2 ? from_integer(0, index_type) : args[2];

  if(c.type().id() == ID_unsignedbv || c.type().id() == ID_signedbv)
  {
    return add_axioms_for_index_of(
      fresh_symbol, str, typecast_exprt(c, char_type), from_index);
  }
  else
  {
    INVARIANT(
      is_refined_string_type(c.type()),
      string_refinement_invariantt(
        "c can only be a (un)signedbv or a refined "
        "string and the (un)signedbv case is already handled"));
    array_string_exprt sub = get_string_expr(array_pool, c);
    return add_axioms_for_index_of_string(fresh_symbol, str, sub, from_index);
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
/// \param fresh_symbol: generator of fresh symbols
/// \param str: an array of characters expression
/// \param c: a character expression
/// \param from_index: an integer expression
/// \return integer expression `index` representing the last index of `needle`
///   in `haystack` before or at `from_index`, or `-1` if there is none
std::pair<exprt, string_constraintst> add_axioms_for_last_index_of(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index)
{
  string_constraintst constraints;
  const typet &index_type = str.length().type();
  const symbol_exprt index = fresh_symbol("last_index_of", index_type);
  const symbol_exprt contains = fresh_symbol("contains_in_last_index_of");

  const exprt minus1 = from_integer(-1, index_type);
  const and_exprt a1(
    binary_relation_exprt(index, ID_ge, minus1),
    binary_relation_exprt(index, ID_le, from_index),
    binary_relation_exprt(index, ID_lt, str.length()));
  constraints.existential.push_back(a1);

  const notequal_exprt a2(contains, equal_exprt(index, minus1));
  constraints.existential.push_back(a2);

  const implies_exprt a3(contains, equal_exprt(str[index], c));
  constraints.existential.push_back(a3);

  const exprt index1 = from_integer(1, index_type);
  const plus_exprt from_index_plus_one(from_index, index1);
  const if_exprt end_index(
    binary_relation_exprt(from_index_plus_one, ID_le, str.length()),
    from_index_plus_one,
    str.length());

  const symbol_exprt n = fresh_symbol("QA_last_index_of1", index_type);
  const string_constraintt a4(
    n,
    zero_if_negative(plus_exprt(index, index1)),
    zero_if_negative(end_index),
    implies_exprt(contains, notequal_exprt(str[n], c)));
  constraints.universal.push_back(a4);

  const symbol_exprt m = fresh_symbol("QA_last_index_of2", index_type);
  const string_constraintt a5(
    m,
    zero_if_negative(end_index),
    implies_exprt(not_exprt(contains), notequal_exprt(str[m], c)));
  constraints.universal.push_back(a5);

  return {index, std::move(constraints)};
}

/// Index of the last occurence of a target inside the string
///
/// If the target is a character:
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_last_index_of(symbol_generatort &fresh_symbol, const array_string_exprt&,const exprt&,const exprt&)
// NOLINTNEXTLINE
/// \link add_axioms_for_last_index_of(symbol_generatort &fresh_symbol, const array_string_exprt&,const exprt&,const exprt&)
///   (More...) \endlink
///
/// If the target is a refined_string:
/// \copybrief add_axioms_for_last_index_of_string
/// \link add_axioms_for_last_index_of_string
///   (More...) \endlink
/// \warning slow for string targets
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `haystack`,
///   refined_string or character `needle`, and optional integer
///   `from_index` with default value `|haystack|-1`
/// \param array_pool: pool of arrays representing strings
/// \return an integer expression
std::pair<exprt, string_constraintst> add_axioms_for_last_index_of(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args = f.arguments();
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt str = get_string_expr(array_pool, args[0]);
  const exprt c = args[1];
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  PRECONDITION(f.type() == index_type);

  const exprt from_index = args.size() == 2 ? str.length() : args[2];

  if(c.type().id() == ID_unsignedbv || c.type().id() == ID_signedbv)
  {
    return add_axioms_for_last_index_of(
      fresh_symbol, str, typecast_exprt(c, char_type), from_index);
  }
  else
  {
    const array_string_exprt sub = get_string_expr(array_pool, c);
    return add_axioms_for_last_index_of_string(
      fresh_symbol, str, sub, from_index);
  }
}
