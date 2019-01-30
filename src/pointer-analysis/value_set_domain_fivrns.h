/*******************************************************************\

Module: Value Set Domain (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set Domain (Flow Insensitive, Validity Regions)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVRNS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVRNS_H

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_fivrns.h"

class value_set_domain_fivrnst:
  public flow_insensitive_abstract_domain_baset
{
public:
  value_set_fivrnst value_set;

  // overloading

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_set.output(ns, out);
  }

  virtual void initialize(
    const namespacet &)
  {
    value_set.clear();
  }

  virtual bool transform(
    const namespacet &ns,
    const irep_idt &function_from,
    locationt from_l,
    const irep_idt &function_to,
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

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_FIVRNS_H
