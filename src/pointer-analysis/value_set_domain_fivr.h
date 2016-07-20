/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef VALUE_SET_DOMAIN_INCR_H_
#define VALUE_SET_DOMAIN_INCR_H_

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_fivr.h"

class value_set_domain_fivrt:public ai_domain_baset
{
public:
  value_set_fivrt value_set;

  // overloading  

  virtual bool merge(const value_set_domain_fivrt &other,    
		     locationt from,
		     locationt to)
  {
    return value_set.handover(); //TODO: Not sure this is correct
  }

  virtual void output(
    std::ostream &out,
    const ai_baset &,
    const namespacet &ns) const
  {
    value_set.output(ns, out);
  }
    
  virtual void initialize(
    const namespacet &ns)
  {
    value_set.clear();    
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns);
  
  virtual void clear( void )
  {
    value_set.clear();
  }
  
};

#endif /*VALUE_SET_DOMAIN_INCR_H_*/
