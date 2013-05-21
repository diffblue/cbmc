/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERVAL_DOMAIN_H
#define CPROVER_INTERVAL_DOMAIN_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>

#include "static_analysis.h"
#include "interval_analysis.h"

class interval_domaint:public domain_baset
{
public:
  // trivial, conjunctive interval domain for both float
  // and integers
  
  struct int_boundt {
    mp_integer lower, upper;
    bool lower_set, upper_set;
    int_boundt():lower_set(false), upper_set(false) { }
  };
  
  struct float_boundt {
    ieee_floatt lower, upper;
    bool lower_set, upper_set;
    float_boundt():lower_set(false), upper_set(false) { }
  };
  
  typedef std::map<irep_idt, int_boundt> int_mapt;
  typedef std::map<irep_idt, float_boundt> float_mapt;

  int_mapt int_map;
  float_mapt float_map;

  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to);
              
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;

  bool merge(const interval_domaint &b);
  
  exprt make_expression() const;
};

#endif
