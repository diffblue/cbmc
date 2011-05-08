/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#include <goto-programs/static_analysis.h>

#include "value_set.h"

class value_set_domaint:public domain_baset
{
public:
  value_sett value_set;

  // overloading  

  virtual bool merge(const value_set_domaint &other)
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
    const namespacet &ns,
    locationt l)
  {
    value_set.clear();
    value_set.location_number=l->location_number;
  }

  virtual void transform(
    const namespacet &ns,
    locationt from_l,
    locationt to_l);

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set.get_reference_set(expr, dest, ns);
  }
  
};

#endif
