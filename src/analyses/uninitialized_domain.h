/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#ifndef CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H
#define CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H

#include <util/threeval.h>

#include "ai.h"

class uninitialized_domaint:public ai_domain_baset
{
public:
  uninitialized_domaint():has_values(false)
  {
  }

  // Locals that are declared but may not be initialized
  typedef std::set<irep_idt> uninitializedt;
  uninitializedt uninitialized;

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  void make_top() final override
  {
    uninitialized.clear();
    has_values=tvt(true);
  }

  void make_bottom() final override
  {
    uninitialized.clear();
    has_values=tvt(false);
  }

  void make_entry() final override
  {
    make_top();
  }

  bool is_top() const override final
  {
    assert(!has_values.is_true() || uninitialized.empty());
    return has_values.is_true();
  }

  bool is_bottom() const override final
  {
    assert(!has_values.is_false() || uninitialized.empty());
    return has_values.is_false();
  }

  // returns true iff there is s.th. new
  bool merge(
    const uninitialized_domaint &other,
    locationt from,
    locationt to);

private:
  tvt has_values;

  void assign(const exprt &lhs);
};

typedef ait<uninitialized_domaint>
  uninitialized_analysist;

#endif // CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H
