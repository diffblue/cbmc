/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#include <util/invariant.h>

#include <analyses/ai.h>

#include "value_set.h"

/// This is the domain for a value set analysis. It is intended to be the
/// template parameter for `value_set_analysis_templatet`, so `VST` would be
/// `value_sett`.
template <class VST>
class value_set_domain_templatet : public ai_domain_baset
{
protected:
  /// ait checks whether domains are bottom to increase speed and accuracy.
  /// Older frameworks don't so it is necessary to track this.
  bool reachable;

public:
  VST value_set;

  explicit value_set_domain_templatet(locationt l) : reachable(false)
  {
    value_set.clear();
    value_set.location_number = l->location_number;
  }

  void make_bottom() override
  {
    reachable = false;
    value_set.clear(); //???
  }

  void make_top() override
  {
    UNREACHABLE;
  }

  void make_entry() override
  {
    reachable = true;
  }

  bool is_bottom() const override
  {
    return reachable == false && value_set.values.size() == 0;
  }

  bool is_top() const override
  {
    return false;
  }

  // overloading

  bool
  merge(const value_set_domain_templatet<VST> &other, trace_ptrt, trace_ptrt)
  {
    reachable |= other.reachable;
    return value_set.make_union(other.value_set);
  }

  void
  output(std::ostream &out, const ai_baset &, const namespacet &) const override
  {
    value_set.output(out);
  }

  void transform(
    const irep_idt &function_from,
    trace_ptrt from,
    const irep_idt &function_to,
    trace_ptrt to,
    ai_baset &ai,
    const namespacet &ns) override;

  void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set.get_reference_set(expr, dest, ns);
  }

  exprt get_return_lhs(locationt to) const
  {
    // get predecessor of "to"
    to--;

    if(to->is_end_function())
      return static_cast<const exprt &>(get_nil_irep());

    INVARIANT(to->is_function_call(), "must be the function call");

    return to->call_lhs();
  }

  xmlt output_xml(const ai_baset &ai, const namespacet &ns) const override
  {
    return value_set.output_xml();
  }
};

typedef value_set_domain_templatet<value_sett> value_set_domaint;

template <class VST>
void value_set_domain_templatet<VST>::transform(
  const irep_idt &,
  trace_ptrt from,
  const irep_idt &function_to,
  trace_ptrt to,
  ai_baset &,
  const namespacet &ns)
{
  if(!reachable)
    return;

  locationt from_l{from->current_location()};
  locationt to_l{to->current_location()};

  switch(from_l->type())
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:
  {
    value_set.do_end_function(get_return_lhs(to_l), ns);
    break;
  }

  // Note intentional fall-through here:
  case SET_RETURN_VALUE:
  case OTHER:
  case ASSIGN:
  case DECL:
  case DEAD:
    value_set.apply_code(from_l->code(), ns);
    break;

  case ASSUME:
    value_set.guard(from_l->condition(), ns);
    break;

  case FUNCTION_CALL:
    value_set.do_function_call(function_to, from_l->call_arguments(), ns);
    break;

  case ASSERT:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
  {
    // do nothing
  }
  }
}

// To pass the correct location to the constructor we need a factory
typedef ai_domain_factory_location_constructort<value_set_domaint>
  value_set_domain_factoryt;

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
