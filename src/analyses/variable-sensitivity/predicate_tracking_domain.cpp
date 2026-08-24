/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: November 2022

\*******************************************************************/

#include "predicate_tracking_domain.h"

#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

void predicate_tracking_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  variable_sensitivity_domaint::output(out, ai, ns);

  out << "{\n";
  for(const auto &pred : predicate_set)
    out << format(pred) << "\n";

  out << "}\n";
}

exprt predicate_tracking_domaint::to_predicate() const
{
  exprt::operandst collected;
  collected.push_back(variable_sensitivity_domaint::to_predicate());
  for(const auto &pred : predicate_set)
    collected.push_back(pred);

  return conjunction(collected);
}

exprt predicate_tracking_domaint::to_predicate(
  const exprt &expr,
  const namespacet &ns) const
{
  // TODO : return all predicates that use a variable from expr
  UNIMPLEMENTED;
  return variable_sensitivity_domaint::to_predicate(expr, ns);
}

exprt predicate_tracking_domaint::to_predicate(
  const exprt::operandst &exprs,
  const namespacet &ns) const
{
  // TODO : return all predicates that use things from the exprs
  UNIMPLEMENTED;
  return variable_sensitivity_domaint::to_predicate(exprs, ns);
}

bool predicate_tracking_domaint::merge(
  const predicate_tracking_domaint &b,
  trace_ptrt from,
  trace_ptrt to)
{
  // We are using the is_bottom tracking from the base
  // which can be altered by the base class merge.
  // So save it here.
  bool this_was_bottom = this->is_bottom();

  // Merge the abstract environments
  bool modified = variable_sensitivity_domaint::merge(b, from, to);

  if(b.is_bottom())
  {
    // Merging with bottom should not change anything
    INVARIANT(modified == false, "base merge should not generate bottom");
    return modified;
  }
  else if(this_was_bottom)
  {
    // Pick up all of the predicates from the other side
    this->predicate_set = b.predicate_set;
  }
  else
  {
    // As we represent bottom with an empty set of predicates
    // we need to avoid pruning here
    INVARIANT(!(this_was_bottom || b.is_bottom()), "Sets are empty");

    // Only keep predicates which are true on both domains
    // Optimisation : iterate over the smallest set
    for(auto it = predicate_set.begin(); it != predicate_set.end(); /* empty */)
    {
      if(b.predicate_set.find(*it) == b.predicate_set.end())
      {
        it = predicate_set.erase(it);
        modified = true;
      }
      else
        ++it;
    }

    // TODO : is it possible to do a meaningful widen for this domain?
  }

  return modified;
}

bool predicate_tracking_domaint::ai_simplify(
  exprt &condition,
  const namespacet &ns) const
{
  // Do the basic context aware simplification first
  bool ret = variable_sensitivity_domaint::ai_simplify(condition, ns);

  // We can only further simplify logical conditions
  if(!can_cast_type<bool_typet>(condition.type()))
    return ret;

  // Do not try to further simplify true or false
  if(condition.is_true() || condition.is_false())
    return ret;

  // Using the predicates in simplification is non-trivial
  // We do the absolute bare minimum by looking up the condition
  // and its negation.
  // ENHANCEMENT : there is a lot more that can be done
  exprt simp_cond = simplify_expr(condition, ns);
  exprt simp_neg = simplify_expr(not_exprt(condition), ns);

  if(predicate_set.find(simp_cond) != predicate_set.end())
  {
    condition = true_exprt();
    return false;
  }
  else if(predicate_set.find(simp_cond) != predicate_set.end())
  {
    condition = false_exprt();
    return false;
  }
  else
    return ret;
}

void predicate_tracking_domaint::merge_three_way_function_return(
  const ai_domain_baset &function_call,
  const ai_domain_baset &function_start,
  const ai_domain_baset &function_end,
  const namespacet &ns)
{
  // TODO : get this working
  UNIMPLEMENTED;
  variable_sensitivity_domaint::merge_three_way_function_return(
    function_call, function_start, function_end, ns);
  return;
}

void predicate_tracking_domaint::assume(exprt expr, namespacet ns)
{
  // Do the basic domain reduction
  variable_sensitivity_domaint::assume(expr, ns);

  // If the domain is bottom then assumptions cannot reduce it further
  if(is_bottom())
    return;

  // If we variable_sensitivity_domaint::ai_simplify(expr) at this point
  // we will see if all of the information is represented and thus avoid
  // tracking predicates like "p == NULL".  This might give a slight
  // performance boost.

  // Simplify to normalise away the most obvious syntactic differences
  exprt simp_cond = simplify_expr(expr, ns);
  exprt simp_neg = simplify_expr(not_exprt(expr), ns);

  // True and false are special cases
  // Note that the checks are not redundant as we can't assume that
  // simplifying one thing to true/false will mean that the negation
  // simplifies to false/true.  It is very likely but not guaranteed.
  if(simp_cond.is_true() || simp_neg.is_false())
    return;

  if(simp_cond.is_false() || simp_neg.is_true())
  {
    make_bottom();
    return;
  }

  // If the negation is true then we will set the domain to bottom
  // This does not do any entailment so adding x > 10 when
  // you already have x < 0 will not result in bottom
  if(predicate_set.find(simp_neg) != predicate_set.end())
  {
    make_bottom();
    return;
  }
  predicate_set.insert(simp_cond);
}

void predicate_tracking_domaint::make_top()
{
  variable_sensitivity_domaint::make_top();
  // Top represents everything so no restrictions hold
  predicate_set.clear();
}

void predicate_tracking_domaint::make_bottom()
{
  variable_sensitivity_domaint::make_bottom();
  // Formally, all possible expressions hold.
  // However we are going to empty the set and
  // check for bottom when merging.
  predicate_set.clear();
}

bool predicate_tracking_domaint::is_bottom() const
{
  // We use the flags from the abstract environment
  bool base = variable_sensitivity_domaint::is_bottom();

  INVARIANT(!base || predicate_set.empty(), "Bottom has empty predicate set");

  return base;
}

bool predicate_tracking_domaint::is_top() const
{
  // We use the flags from the abstract environment
  bool base = variable_sensitivity_domaint::is_top();

  // Not top if there are predicates
  return base && predicate_set.empty();
}

// Need to remove predicates which are no longer true after the assignment.
// This is currently a very crude over-estimate.
// A better approach is to keep p(x) when p(x) => p(rhs)
bool predicate_tracking_domaint::assign(
  const exprt &expr,
  const abstract_object_pointert &value,
  const namespacet &ns)
{
  bool res = variable_sensitivity_domaint::assign(expr, value, ns);

  // TODO : finer grain handling of structures, unions and arrays so
  // that writing to a[1].x does not invalidate a[0].x or a[1].y
  //
  // TODO : check this works with pointers

  const auto lhs_symbols = find_symbols(expr);

  for(auto it = predicate_set.begin(); it != predicate_set.end(); /* empty */)
  {
    // Optimisation : this can be cached and turned into lookup tables
    const auto pred_symbols = find_symbols(*it);
    std::set<symbol_exprt> intersection;

    std::set_intersection(
      lhs_symbols.cbegin(),
      lhs_symbols.cend(),
      pred_symbols.cbegin(),
      pred_symbols.cend(),
      std::inserter(intersection, intersection.end()));

    if(intersection.size() > 0)
    {
      it = predicate_set.erase(it);
      res |= true;
    }
    else
      ++it;
  }

  return res;
}
