/*******************************************************************\

Module: Defines related function for string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H

#include <set>

#include <util/std_expr.h>

class string_constraintt;
struct string_not_contains_constraintt;

/// Instantiates a string constraint by substituting the quantifiers.
/// For a string constraint of the form \f$\forall q. P(x)\f$,
/// substitute `q` the universally quantified variable of `axiom`, by
/// an `index`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` corresponds to \f$\forall q.\ s[q+x]='a' \land
/// t[q]='b'\f$, `instantiate(axiom,s,v)` would return an expression for
/// \f$s[v]='a' \land t[v-x]='b'\f$.
/// If there are several such indexes, the conjunction of the instantiations is
/// returned, for instance for a formula:
/// \f$\forall q. s[q+x]='a' \land s[q]=c\f$ we would get
/// \f$s[v] = 'a' \land s[v-x] = c \land s[v+x] = 'a' \land s[v] = c\f$.
/// \param axiom: a universally quantified formula
/// \param str: an array of characters
/// \param val: an index expression
/// \return `axiom` with substitued `qvar`
exprt instantiate(
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val);

std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<std::pair<exprt, exprt>> &index_pairs,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses);

/// Canonical representation of linear function, for instance, expression
/// $x + x - y + 5 - 3$ would given by \c constant_coefficient 2 and
/// \p coefficients: x -> 2, y -> -1
class linear_functiont
{
public:
  /// Put an expression \p f composed of additions and subtractions into
  /// its cannonical representation
  explicit linear_functiont(const exprt &f);

  /// Make this function the sum of the current function with \p other
  void add(const linear_functiont &other);

  /// \param negated: optional Boolean asking to negate the function
  /// \return an expression corresponding to the linear function
  exprt to_expr(bool negated = false) const;

  /// Return an expression `y` such that `f(var <- y) = val`.
  /// The coefficient of \p var in the linear function must be 1 or -1.
  /// For instance, if `f` corresponds to the expression `q + x`, `solve(q,v,f)`
  /// returns the expression `v - x`.
  static exprt solve(linear_functiont f, const exprt &var, const exprt &val);

  /// Format the linear function as a string, can be used for debugging
  std::string format();

private:
  mp_integer constant_coefficient;
  std::unordered_map<exprt, mp_integer, irep_hash> coefficients;
  typet type;
};

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
