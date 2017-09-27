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

#include "bv_refinement.h"
#include "string_refinement_invariant.h"

#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>
#include <langapi/language_util.h>
#include <java_bytecode/java_types.h>
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
  // forall univ_var in [lower_bound,upper_bound[. premise => body
  exprt premise = true_exprt(); // Index guard
  exprt body;                   // value constraint
  symbol_exprt univ_var;
  // \todo avoid depending on java type
  exprt lower_bound = from_integer(0, java_int_type());
  exprt upper_bound;
};

inline void
replace(string_constraintt &axiom, const union_find_replacet &symbol_resolve)
{
  symbol_resolve.replace_expr(axiom.premise);
  symbol_resolve.replace_expr(axiom.body);
  symbol_resolve.replace_expr(axiom.univ_var);
  symbol_resolve.replace_expr(axiom.upper_bound);
  symbol_resolve.replace_expr(axiom.lower_bound);
}

exprt univ_within_bounds(const string_constraintt &axiom);

/// Used for debug printing.
/// \param [in] ns: namespace for `from_expr`
/// \param [in] identifier: identifier for `from_expr`
/// \param [in] expr: constraint to render
/// \return rendered string
std::string to_string(const string_constraintt &expr);

/// Checks the data invariant for \link string_constraintt
/// \related string_constraintt
/// \param [in] constraint: the string constraint to check
/// \return whether the constraint satisfies the invariant
bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &constraint);

/// Constraints to encode non containement of strings.
class string_not_contains_constraintt final : public exprt
{
public:
  // string_not contains_constraintt are formula of the form:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s0[x+y] != s1[y]

  string_not_contains_constraintt(
    exprt univ_lower_bound,
    exprt univ_bound_sup,
    exprt premise,
    exprt exists_bound_inf,
    exprt exists_bound_sup,
    const array_string_exprt &s0,
    const array_string_exprt &s1)
    : exprt(ID_string_not_contains_constraint)
  {
    copy_to_operands(univ_lower_bound, univ_bound_sup, premise);
    copy_to_operands(exists_bound_inf, exists_bound_sup, s0);
    copy_to_operands(s1);
  };

  const exprt &univ_lower_bound() const
  {
    return op0();
  }

  const exprt &univ_upper_bound() const
  {
    return op1();
  }

  const exprt &premise() const
  {
    return op2();
  }

  const exprt &exists_lower_bound() const
  {
    return op3();
  }

  const exprt &exists_upper_bound() const
  {
    return operands()[4];
  }

  const array_string_exprt &s0() const
  {
    return to_array_string_expr(operands()[5]);
  }

  const array_string_exprt &s1() const
  {
    return to_array_string_expr(operands()[6]);
  }
};

/// Used for debug printing.
/// \param [in] ns: namespace for `from_expr`
/// \param [in] identifier: identifier for `from_expr`
/// \param [in] expr: constraint to render
/// \return rendered string
std::string to_string(const string_not_contains_constraintt &expr);

const string_not_contains_constraintt &
to_string_not_contains_constraint(const exprt &expr);

string_not_contains_constraintt &to_string_not_contains_constraint(exprt &expr);

#endif
