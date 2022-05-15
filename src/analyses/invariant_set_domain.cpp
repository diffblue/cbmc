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
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from_l(trace_from->current_location());
  locationt to_l(trace_to->current_location());

  switch(from_l->type())
  {
  case GOTO:
    {
      // Comparing iterators is safe as the target must be within the same list
      // of instructions because this is a GOTO.
      exprt tmp(from_l->condition());

      if(std::next(from_l) == to_l)
        tmp = boolean_negate(tmp);

      simplify(tmp, ns);
      invariant_set.strengthen(tmp);
    }
    break;

  case ASSERT:
  case ASSUME:
    {
      exprt tmp(from_l->condition());
      simplify(tmp, ns);
      invariant_set.strengthen(tmp);
    }
    break;

    case SET_RETURN_VALUE:
      // ignore
      break;

    case ASSIGN:
      invariant_set.assignment(from_l->assign_lhs(), from_l->assign_rhs());
      break;

    case OTHER:
      if(from_l->get_other().is_not_nil())
        invariant_set.apply_code(from_l->code());
      break;

    case DECL:
      invariant_set.apply_code(from_l->code());
      break;

    case FUNCTION_CALL:
      invariant_set.apply_code(from_l->code());
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
