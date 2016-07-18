/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#include <analyses/ai.h>
#include <util/config.h>

#include "value_set.h"

class value_set_domaint:public ai_domain_baset
{
public:
  value_set_domaint(bool _use_top=true)
    : ai_domain_baset(), value_set(_use_top)
  {}
  
  value_sett value_set;

  // overloading  

  inline bool merge(const value_set_domaint &other, 
		            locationt from, locationt to)
  {
    return value_set.make_union(other.value_set);
  }

  bool merge_shared(
    const value_set_domaint &other,
    locationt from, locationt to,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const
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
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns);

  virtual void transform_internal(
    locationt from_l,
    locationt to_l,
    unsigned dynamic_object_number,
    ai_baset &ai,
    const namespacet &ns);

  virtual void make_bottom()
  {
    value_set.clear();
  }

  virtual void make_top()
  {
    value_set.make_any();
  }

  size_t hash() const
  {
    return value_set.hash();
  }

  bool operator==(const value_set_domaint &other) const
  {
    return value_set==other.value_set;
  }

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    assert(false);
    value_set.get_reference_set(expr, dest, ns);
  }
  
  // get lhs that return value is assigned to
  // for an edge that returns from a function
  static exprt get_return_lhs(locationt to);
  
protected:
  bool is_shared(
    const irep_idt &identifer,
    const namespacet &ns);
};


#endif
