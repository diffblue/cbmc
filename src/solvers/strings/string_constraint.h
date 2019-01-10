/*******************************************************************\

Module: Defines string constraints. These are formulas talking about strings.
        We implemented two forms of constraints: `string_constraintt`
        are formulas of the form $\forall univ_var \in [lb,ub[. prem => body$,
        and not_contains_constraintt of the form:
        $\forall x in [lb,ub[. p(x) => \exists y in [lb,ub[. s1[x+y] != s2[y]$.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Defines string constraints. These are formulas talking about strings.  We
///   implemented two forms of constraints: `string_constraintt`  are formulas
///   of the form \f$\forall univ\_var \in [lb,ub[. prem => body\f$, and
///   not_contains_constraintt of the form: \f$\forall x \in [lb,ub[. p(x) =>
///   \exists y \in [lb,ub[. s1[x+y] \ne s2[y]\f$.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H

#include "string_refinement_invariant.h"

#include <solvers/refinement/bv_refinement.h>

#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>
#include <util/union_find_replace.h>

///  ### Universally quantified string constraint
///
///  This represents a universally quantified string constraint as laid out in
///  DOI: 10.1007/978-3-319-03077-7. The paper seems to specify a universal
///  constraint as follows.
///
///  A universal constraint is of the form
///  \f$ \forall i.\ PI(i) \Rightarrow  PV(i)\f$
///  where \f$PI\f$ and \f$PV\f$ satisfies the following conditions:
///
///    * The predicate `PI` , called the index guard, must follow the grammar
///      * \f$iguard : iguard \land iguard \mid iguard \lor iguard \mid
///        iterm \le iterm \mid  iterm = iterm \f$
///      * \f$iterm : integer\_constant1 \times i + integer\_constant2 \f$
///
///    * The predicate `PV` is called the value constraint.
///      The index variable `i` can only be used in array read expressions of
///      the form `a[i]`.
///      ie. `PV` is of the form \f$P'(s_0[f_0(i)],\ldots, s_k[f_k(i)]
///      )\f$, moreover when focusing on one specific string, all indices are
///      the same [stated in a roundabout manner].
///      \f$L(n)\f$ and \f$P(n, s_0,\ldots, s_k)\f$ may contain other (free)
///      variables, but in \f$P\f$, \f$n\f$ can only occur as an argument to an
///      \f$f\f$ [explicitly stated, implied].
///
/// \todo The fact that we follow this grammar is not enforced at the moment.
class string_constraintt final
{
public:
  // String constraints are of the form
  // forall univ_var in [lower_bound,upper_bound[. body
  symbol_exprt univ_var;
  exprt lower_bound;
  exprt upper_bound;
  exprt body;

  string_constraintt() = delete;

  string_constraintt(
    const symbol_exprt &_univ_var,
    const exprt &lower_bound,
    const exprt &upper_bound,
    const exprt &body);

  // Default bound inferior is 0
  string_constraintt(symbol_exprt univ_var, exprt upper_bound, exprt body)
    : string_constraintt(
        univ_var,
        from_integer(0, univ_var.type()),
        upper_bound,
        body)
  {
  }

  exprt univ_within_bounds() const
  {
    return and_exprt(
      binary_relation_exprt(lower_bound, ID_le, univ_var),
      binary_relation_exprt(upper_bound, ID_gt, univ_var));
  }

  void replace_expr(union_find_replacet &replace_map)
  {
    replace_map.replace_expr(lower_bound);
    replace_map.replace_expr(upper_bound);
    replace_map.replace_expr(body);
  }

  exprt negation() const
  {
    return and_exprt(univ_within_bounds(), not_exprt(body));
  }
};

/// Used for debug printing.
/// \param expr: constraint to render
/// \return rendered string
inline std::string to_string(const string_constraintt &expr)
{
  std::ostringstream out;
  out << "forall " << format(expr.univ_var) << " in ["
      << format(expr.lower_bound) << ", " << format(expr.upper_bound) << "). "
      << format(expr.body);
  return out.str();
}

/// Constraints to encode non containement of strings.
/// string_not contains_constraintt are formulas of the form:
/// ```
/// forall x in [univ_lower_bound, univ_upper_bound[.
///   premise(x) =>
///     exists y in [exists_lower_bound, exists_upper_bound[. s0[x+y] != s1[y]
/// ```
struct string_not_contains_constraintt
{
  exprt univ_lower_bound;
  exprt univ_upper_bound;
  exprt premise;
  exprt exists_lower_bound;
  exprt exists_upper_bound;
  array_string_exprt s0;
  array_string_exprt s1;
};

std::string to_string(const string_not_contains_constraintt &expr);

void replace(
  const union_find_replacet &replace_map,
  string_not_contains_constraintt &constraint);

bool operator==(
  const string_not_contains_constraintt &left,
  const string_not_contains_constraintt &right);

// NOLINTNEXTLINE [allow specialization within 'std']
namespace std
{
template <>
// NOLINTNEXTLINE [struct identifier 'hash' does not end in t]
struct hash<string_not_contains_constraintt>
{
  size_t operator()(const string_not_contains_constraintt &constraint) const
  {
    return irep_hash()(constraint.univ_lower_bound) ^
           irep_hash()(constraint.univ_upper_bound) ^
           irep_hash()(constraint.exists_lower_bound) ^
           irep_hash()(constraint.exists_upper_bound) ^
           irep_hash()(constraint.premise) ^ irep_hash()(constraint.s0) ^
           irep_hash()(constraint.s1);
  }
};
}

#endif
