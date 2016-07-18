/*******************************************************************\

Module: Value Set Domain (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#include "value_set_domain_cs.h"

void value_set_domain_cst::transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns)
{
  unsigned dynamic_object_number=ai.get_stack_number(stack);
  base.transform_internal(from_l, to_l, dynamic_object_number, dummy, ns);
}

void value_set_domain_cst::output(
  std::ostream &out,
  const ai_cs_baset &ai,
  const namespacet &ns) const
{
  base.output(out, dummy, ns);
}
