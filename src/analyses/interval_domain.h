/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_INTERVAL_DOMAIN_H
#define CPROVER_ANALYSES_INTERVAL_DOMAIN_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>

#include "ai.h"
#include "interval_template.h"

typedef interval_template<mp_integer> integer_intervalt;
typedef interval_template<ieee_floatt> ieee_float_intervalt;

class interval_domaint:public ai_domain_baset
{
public:
  // Trivial, conjunctive interval domain for both float
  // and integers. The categorization 'float' and 'integers'
  // is done by is_int and is_float.

  interval_domaint():bottom(true)
  {
  }

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  bool join(const interval_domaint &b);

  bool merge(
    const interval_domaint &b,
    locationt from,
    locationt to)
  {
    return join(b);
  }

  // no states
  void make_bottom() final
  {
    int_map.clear();
    float_map.clear();
    bottom=true;
  }

  // all states
  void make_top() final
  {
    int_map.clear();
    float_map.clear();
    bottom=false;
  }

  void make_entry() final
  {
    make_top();
  }

  exprt make_expression(const symbol_exprt &) const;

  void assume(const exprt &, const namespacet &);

  static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }

  static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

  bool is_bottom() const
  {
    return bottom;
  }

  virtual bool ai_simplify(
    exprt &condition,
    const namespacet &ns,
    const bool lhs=false) const;

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

#endif // CPROVER_ANALYSES_INTERVAL_DOMAIN_H
