/*******************************************************************\

Module: Invariant Set Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "invariant_set_domain.h"

/*******************************************************************\

Function: invariant_set_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_set_domaint::transform(
  locationt from_l,
  locationt to_l,
  ai_baset &ai,
  const namespacet &ns)
{
  switch(from_l->type)
  {
  case GOTO:
    {
      exprt tmp(from_l->guard);

      goto_programt::const_targett next=from_l;
      next++;
      if(next==to_l) tmp.make_not();

      simplify(tmp, ns);
      invariant_set.strengthen(tmp);
    }
    break;

  case ASSERT:
  case ASSUME:
    {
      exprt tmp(from_l->guard);
      simplify(tmp, ns);
      invariant_set.strengthen(tmp);
    }
    break;

  case RETURN:
    // ignore
    break;

  case ASSIGN:
    {
      const code_assignt &assignment=to_code_assign(from_l->code);
      invariant_set.assignment(assignment.lhs(), assignment.rhs());
    }
    break;

  case OTHER:
    if(from_l->code.is_not_nil())
      invariant_set.apply_code(from_l->code);
    break;

  case DECL:
    invariant_set.apply_code(from_l->code);
    break;

  case FUNCTION_CALL:
    invariant_set.apply_code(from_l->code);
    break;

  case START_THREAD:
    invariant_set.make_threaded();
    break;

  default:;
    // do nothing
  }
}
