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
#include "intervals.h"

class interval_domaint:public domain_baset
{
public:
  // trivial, conjunctive interval domain for both float
  // and integers
  
  typedef std::map<irep_idt, integer_intervalt> int_mapt;
  typedef std::map<irep_idt, ieee_float_intervalt> float_mapt;

  int_mapt int_map;
  float_mapt float_map;

  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to);
              
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;

  bool merge(const interval_domaint &b, locationt to);
  
  exprt make_expression(const symbol_exprt &) const;
  
  static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }
  
  static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

protected:
  void havoc_rec(const exprt &);
  void assume_rec(const exprt &, bool negation=false);
  void assume_rec(const exprt &lhs, irep_idt id, const exprt &rhs);
  void assign(const class code_assignt &assignment);
  integer_intervalt get_int_rec(const exprt &);
  ieee_float_intervalt get_float_rec(const exprt &);
};

#endif
