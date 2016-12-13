/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_INVARIANT_SET_DOMAIN_H
#define CPROVER_ANALYSES_INVARIANT_SET_DOMAIN_H

#include "ai.h"
#include "invariant_set.h"

class invariant_set_domaint:public ai_domain_baset
{
public:
  invariant_sett invariant_set;

  // overloading

  inline bool merge(
    const invariant_set_domaint &other,
    locationt from,
    locationt to)
  {
    return invariant_set.make_union(other.invariant_set);
  }

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override final
  {
    invariant_set.output("", out);
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns) override final;
    
  void make_top() override final
  {
    invariant_set.make_true();
  }

  void make_bottom() override final
  {
    invariant_set.make_false();
  }

  void make_entry() override final
  {
    invariant_set.make_true();
  }
};

#endif // CPROVER_ANALYSES_INVARIANT_SET_DOMAIN_H
