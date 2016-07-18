/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_INVARIANT_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_INVARIANT_SET_DOMAIN_H

#include "ai.h"
#include "invariant_set.h"

class invariant_set_domaint:public ai_domain_baset
{
public:
  invariant_sett invariant_set;

  // overloading  

  inline bool merge(const invariant_set_domaint &other, 
		    locationt from, locationt to)
  {
    return invariant_set.make_union(other.invariant_set);
  }

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    invariant_set.output("", out);
  }
    
  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
    invariant_set.make_true();
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns);

protected:
  exprt get_guard(
    locationt from,
    locationt to);

};

#endif
