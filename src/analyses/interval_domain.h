/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interval Domain

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
    const namespacet &ns) final override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

protected:
  bool join(const interval_domaint &b);

public:
  bool merge(
    const interval_domaint &b,
    locationt from,
    locationt to)
  {
    return join(b);
  }

  virtual std::vector<symbol_exprt> get_modified_symbols(const interval_domaint &other) const
  {
    return std::vector<symbol_exprt>();
  }

  void restore_domain(std::vector<symbol_exprt> modified_symbols, 
     interval_domaint &target_domain, const namespacet ns) const
  {
    
  }

  // no states
  void make_bottom() final override
  {
    int_map.clear();
    float_map.clear();
    bottom=true;
  }

  // all states
  void make_top() final override
  {
    int_map.clear();
    float_map.clear();
    bottom=false;
  }

  void make_entry() final override
  {
    make_top();
  }

  bool is_bottom() const override final
  {
    // assert(!bottom || (int_map.empty() && float_map.empty()));

    return bottom;
  }

  bool is_top() const override final
  {
    return !bottom && int_map.empty() && float_map.empty();
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

  virtual bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const override;

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
