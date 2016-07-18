/*******************************************************************\

Module: Value Set Domain (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_
#define __CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_fivrns.h"

class value_set_domain_fivrnst : 
  public ai_domain_baset
{
public:
  value_set_fivrnst value_set;

  // overloading  

  virtual bool merge(const value_set_domain_fivrnst &other,    
		     locationt from,
		     locationt to)
  {
    return value_set.handover(); //TODO: Not sure this is correct
  }

  virtual void output(
    std::ostream &out,
    ai_baset &ai,
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

#endif /*__CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_*/
