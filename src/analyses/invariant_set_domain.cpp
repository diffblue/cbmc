/*******************************************************************\

Module: Invariant Set Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Set Domain

#include "invariant_set_domain.h"

#include <util/simplify_expr.h>

void invariant_set_domaint::transform(
  const irep_idt &,
  locationt from_l,
  const irep_idt &,
  locationt to_l,
  ai_baset &,
  const namespacet &ns)
{
  switch(from_l->type)
  {
  case GOTO:
    {
      // Comparing iterators is safe as the target must be within the same list
      // of instructions because this is a GOTO.
      exprt tmp(from_l->guard);

      goto_programt::const_targett next=from_l;
      next++;
      if(next==to_l)
        tmp.make_not();

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

  default:
    {
      // do nothing
    }
  }
}
