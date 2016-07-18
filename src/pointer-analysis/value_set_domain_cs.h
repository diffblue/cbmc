/*******************************************************************\

Module: Value Set Domain (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_CS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_CS_H

#include <analyses/ai_cs.h>

#include "value_set_domain.h"
#include "value_set_analysis.h"

class value_set_domain_cst:public ai_cs_domain_baset
{
public:
  value_set_domaint base;

  // base domain wrapper

  inline bool merge(const value_set_domain_cst &other, 
		    locationt from, locationt to, const ai_cs_stackt &stack)
  {
    return base.merge(other.base, from, to);
  }
  
  bool merge_shared(
    const value_set_domain_cst &other,
    locationt from, locationt to,
    const namespacet &ns)
  {
    return base.merge_shared(other.base, from, to, ns);
  }

  virtual void output(
    std::ostream &out,
    const ai_cs_baset &ai,
    const namespacet &ns) const;
    
  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
    base.initialize(ns, l);
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns);

  virtual void make_bottom()
  {
    base.make_bottom();
  }

  virtual void make_top()
  {
    base.make_top();
  }

  size_t hash() const
  {
    return base.hash();
  }

  bool operator==(const value_set_domain_cst &other) const
  {
    return base==other.base;
  }

private:
  value_set_analysist dummy; // TODO: this is not nice
};

struct value_set_domain_cs_hasht
{
  size_t operator()(const value_set_domain_cst &v) const
  {
    return v.hash();
  }
};

#endif
