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

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_set.output(ns, out);
  }

  virtual void initialize(
    const namespacet &,
    locationt l)
  {
    value_set.clear();
    value_set.location_number=l->location_number;
  }

  virtual void transform(
    const namespacet &ns,
    const irep_idt &function_from,
    locationt from_l,
    const irep_idt &function_to,
    locationt to_l);

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set.get_reference_set(expr, dest, ns);
  }
};

typedef value_set_domain_templatet<value_sett> value_set_domaint;

#include "value_set_domain_transform.inc"

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
