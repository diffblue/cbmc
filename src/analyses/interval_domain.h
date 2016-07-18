/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERVAL_DOMAIN_H
#define CPROVER_INTERVAL_DOMAIN_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>
#include <util/interval_template.h>

#include "ai.h"
#include "interval_analysis.h"
#include "intervals.h"

typedef interval_template<mp_integer> integer_intervalt;
typedef interval_template<ieee_floatt> ieee_float_intervalt;

class interval_domaint:public ai_domain_baset
{
public:
  // Trivial, conjunctive interval domain for both float
  // and integers. The categorization 'float' and 'integers'
  // is done by is_int and is_float.
  
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);
              
  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const interval_domaint &b,
    locationt from,
    locationt to);
  
  // no states
  virtual void make_bottom()
  {
    int_map.clear();
    float_map.clear();
    bottom=true;
  }
        
  // all states
  virtual void make_top()
  {
    int_map.clear();
    float_map.clear();
    bottom=false;
  }

  exprt make_expression(const symbol_exprt &) const;
  
  void assume(const exprt &, const namespacet &);

  inline static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }
  
  inline static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

  inline bool is_bottom() const
  {
    return bottom;
  }

protected:
  bool bottom;

  typedef std::map<irep_idt, integer_intervalt> int_mapt;
  typedef std::map<irep_idt, ieee_float_intervalt> float_mapt;

  int_mapt int_map;
  float_mapt float_map;

  void havoc_rec(const exprt &);
  void assume_rec(const exprt &, bool negation=false);
  void assume_rec(const exprt &lhs, irep_idt id, const exprt &rhs);
  void assign(const class code_assignt &assignment);
  integer_intervalt get_int_rec(const exprt &);
  ieee_float_intervalt get_float_rec(const exprt &);
};

#endif
