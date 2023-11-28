/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H

#include <analyses/ai.h>

#include "value_set_domain.h" // IWYU pragma: keep
#include "value_sets.h"

/// This template class implements a data-flow analysis which keeps track of
/// what values different variables might have at different points in the
/// program. It is used through the alias `value_set_analysist`, so `VSDT` is
/// `value_set_domain_templatet<value_sett>`.
template <class VSDT>
class value_set_analysis_templatet : public value_setst, public ait<VSDT>
{
private:
  const namespacet &ns;

public:
  typedef VSDT domaint;
  typedef ait<domaint> baset;
  typedef typename baset::locationt locationt;

  explicit value_set_analysis_templatet(const namespacet &_ns)
    : baset(std::make_unique<ai_domain_factory_location_constructort<VSDT>>()),
      ns(_ns)
  {
  }

  // interface value_sets
  std::vector<exprt>
  get_values(const irep_idt &, locationt l, const exprt &expr) override
  {
    auto s = this->abstract_state_before(l);
    auto d = std::dynamic_pointer_cast<const domaint>(s);
    return d->value_set.get_value_set(expr, ns);
  }
};

typedef
  value_set_analysis_templatet<value_set_domain_templatet<value_sett>>
  value_set_analysist;

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
