/*******************************************************************\

Module: Value Set (Flow Insensitive)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef VALUE_SET_DOMAIN_FI_H_
#define VALUE_SET_DOMAIN_FI_H_

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_fi.h"

class value_set_domain_fit:public ai_domain_baset
{
public:
  value_set_fit value_set;

  // overloading  

  virtual bool merge(const value_set_domain_fit &other,    
		     locationt from,
		     locationt to)
  {
    return value_set.make_union(other.value_set);
  }
    
  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const
  {
    value_set.output(ns, out);
  }

  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);
  
  virtual void clear( void )
  {
    value_set.clear();
  }
  
};

#endif /*VALUE_SET_DOMAIN_FI_H_*/
