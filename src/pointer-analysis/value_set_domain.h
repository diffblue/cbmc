/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#include "value_set.h"

#include <analyses/ai.h>

template<class VST>
class value_set_domain_templatet : public ai_domain_baset
{
public:
  VST value_set;

  value_set_domain_templatet() : state_is_bottom(false)
  {
  }

  // overloading

  bool merge(
    const value_set_domain_templatet<VST> &other, locationt from, locationt to)
  {
    bool ret = state_is_bottom;
    state_is_bottom = false;
    ret |= value_set.make_union(other.value_set);
    return ret;
  }

  virtual void output(
    std::ostream &out,
    const ai_baset &value_set_analysis,
    const namespacet &ns) const override
  {
    value_set.output(ns, out);
  }

  virtual void make_top() override
  {
    value_set.clear();
    state_is_bottom = false;
  }

  virtual void make_bottom() override
  {
    value_set.clear();
    state_is_bottom = true;
  }

  virtual void make_entry() override
  {
    make_top();
  }

  virtual bool is_bottom() const override
  {
    return value_set.values.empty() && state_is_bottom;
  }

  virtual bool is_top() const override
  {
    return value_set.values.empty() && !state_is_bottom;
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns) override;

  void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set.get_reference_set(expr, dest, ns);
  }

private:
  bool state_is_bottom;
};

typedef value_set_domain_templatet<value_sett> value_set_domaint;

#include "value_set_domain_transform.inc"

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
