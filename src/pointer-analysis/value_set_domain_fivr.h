/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set (Flow Insensitive, Sharing, Validity Regions)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVR_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVR_H

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_fivr.h"

class value_set_domain_fivrt:public flow_insensitive_abstract_domain_baset
{
public:
  value_set_fivrt value_set;

  // overloading

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_set.output(ns, out);
  }

  virtual void initialize(
    const namespacet &ns)
  {
    value_set.clear();
  }

  virtual bool transform(
    const namespacet &ns,
    locationt from_l,
    locationt to_l);

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    expr_sett &expr_set)
  {
    value_set.get_reference_set(expr, expr_set, ns);
  }

  virtual void clear(void)
  {
    value_set.clear();
  }
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVR_H
