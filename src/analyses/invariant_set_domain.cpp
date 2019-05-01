/*******************************************************************\

Module: Invariant Set Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Set Domain

#include "invariant_set_domain.h"

#include <util/expr_util.h>
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
      exprt tmp(from_l->get_condition());

      if(std::next(from_l) == to_l)
        tmp = boolean_negate(tmp);

      simplify(tmp, ns);
      invariant_set.strengthen(tmp);
    }
    break;

  case ASSERT:
  case ASSUME:
    {
      exprt tmp(from_l->get_condition());
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
    if(from_l->get_other().is_not_nil())
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

  case CATCH:
  case THROW:
    DATA_INVARIANT(false, "Exceptions must be removed before analysis");
    break;
  case DEAD:         // No action required
  case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
  case ATOMIC_END:   // Ignoring is a valid over-approximation
  case END_FUNCTION: // No action required
  case LOCATION:     // No action required
  case END_THREAD:   // Require a concurrent analysis at higher level
  case SKIP:         // No action required
    break;
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    DATA_INVARIANT(false, "Only complete instructions can be analyzed");
    break;
  }
}
