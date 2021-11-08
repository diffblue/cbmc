/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include <analyses/static_analysis.h>

#include "value_set.h"

/// This is the domain for a value set analysis. It is intended to be the
/// template parameter for `value_set_analysis_templatet`, so `VST` would be
/// `value_sett`.
template<class VST>
class value_set_domain_templatet:public domain_baset
{
public:
  VST value_set;

  // overloading

  bool merge(const value_set_domain_templatet<VST> &other, locationt)
  {
    return value_set.make_union(other.value_set);
  }

  void output(const namespacet &, std::ostream &out) const override
  {
    value_set.output(out);
  }

  void initialize(const namespacet &, locationt l) override
  {
    value_set.clear();
    value_set.location_number=l->location_number;
  }

  void transform(
    const namespacet &ns,
    const irep_idt &function_from,
    locationt from_l,
    const irep_idt &function_to,
    locationt to_l) override;

  void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest) override
  {
    value_set.get_reference_set(expr, dest, ns);
  }
};

typedef value_set_domain_templatet<value_sett> value_set_domaint;

template <class VST>
void value_set_domain_templatet<VST>::transform(
  const namespacet &ns,
  const irep_idt &,
  locationt from_l,
  const irep_idt &function_to,
  locationt to_l)
{
  switch(from_l->type())
  {
  case ASSIGN:
    value_set.assign(
      from_l->assign_lhs(), from_l->assign_rhs(), ns, false, false);
    break;

  case DEAD:
    // ignore for now (could prune value set)
    break;

  case DECL:
    value_set.apply_decl(from_l->decl_symbol(), ns);
    break;

  case END_FUNCTION:
    value_set.do_end_function(static_analysis_baset::get_return_lhs(to_l), ns);
    break;

  case GOTO:
    // ignore for now
    break;

  case SET_RETURN_VALUE:
    value_set.apply_set_return_value(from_l->return_value(), ns);
    break;

  case OTHER:
    // ignore
    break;

  case ASSUME:
    value_set.guard(from_l->get_condition(), ns);
    break;

  case FUNCTION_CALL:
    value_set.do_function_call(function_to, from_l->call_arguments(), ns);
    break;

  case ASSERT:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
  {
    // do nothing
  }
  }
}

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
