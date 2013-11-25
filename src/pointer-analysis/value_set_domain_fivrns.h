/*******************************************************************\

Module: Value Set Domain (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_
#define __CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_

#include <goto-programs/flow_insensitive_analysis.h>

#include "value_set_fivrns.h"

class value_set_domain_fivrnst : 
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
  
  virtual void clear( void )
  {
    value_set.clear();
  }
  
};

#endif /*__CPROVER_VALUE_SET_DOMAIN_FIVRNS_H_*/
