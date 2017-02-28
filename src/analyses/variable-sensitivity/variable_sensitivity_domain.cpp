/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

\*******************************************************************/


#include <util/message.h>

#include "variable_sensitivity_domain.h"

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: variable_sensitivity_domaint::transform

  Inputs: The instruction before (from) and after (to) the abstract domain,
          the abstract interpreter (ai) and the namespace (ns).

 Outputs: None

 Purpose: Compute the abstract transformer for a single instruction

\*******************************************************************/

void variable_sensitivity_domaint::transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << "Transform from/to:\n";
  std::cout << from->location_number << " --> "
            << to->location_number << std::endl;
  #endif

  const goto_programt::instructiont &instruction=*from;
  switch(instruction.type)
  {
  case DECL:
    // Creates a new variable, which should be top
    // but we don't store top so ... no action required
    break;

  case DEAD:
    {
    // Assign to top is the same as removing
    abstract_object_pointert top_object=
      abstract_state.abstract_object_factory(
        to_code_dead(instruction.code).symbol().type(), ns, true);
    abstract_state.assign(
      to_code_dead(instruction.code).symbol(), top_object, ns);
    }
    break;

  case ASSIGN:
    {
      const code_assignt &inst = to_code_assign(instruction.code);

      // TODO : check return values
      abstract_object_pointert r = abstract_state.eval(inst.rhs(), ns);
      abstract_state.assign(inst.lhs(), r, ns);
    }
    break;

  case GOTO:
    {
      // TODO(tkiley): add support for flow sensitivity
      if (1) // (flow_sensitivity == FLOW_SENSITIVE)
      {
        locationt next=from;
        next++;
        if(next==to)
          abstract_state.assume(not_exprt(instruction.guard), ns);
        else
          abstract_state.assume(instruction.guard, ns);
      }
    }
    break;

  case ASSUME:
    abstract_state.assume(instruction.guard, ns);
    break;

  case FUNCTION_CALL:
    // FIXME : Ignore as not yet interprocedural
    break;

  case END_FUNCTION:
    // FIXME : Ignore as not yet interprocedural
    break;

    /***************************************************************/

  case ASSERT:
    // Conditions on the program, do not alter the data or information
    // flow and thus can be ignored.
    // Checking of assertions can only be reasonably done once the fix-point
    // has been computed, i.e. after all of the calls to transform.
    break;

  case SKIP:
  case LOCATION:
    // Can ignore
    break;

  case RETURN:
    throw "return instructions should be removed first";

  case START_THREAD:
  case END_THREAD:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    throw "threading not supported";

  case THROW:
  case CATCH:
    throw "exceptions not handled";

  case OTHER:
//    throw "other";
      break;

  default:
    throw "unrecognised instruction type";
  }
}

/*******************************************************************\

Function: variable_sensitivity_domaint::output

  Inputs: The output stream (out), the abstract interpreter (ai) and
          the namespace.

 Outputs: None

 Purpose: Basic text output of the abstract domain

\*******************************************************************/
void variable_sensitivity_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  abstract_state.output(out, ai, ns);
}

/*******************************************************************\

Function: variable_sensitivity_domaint::make_bottom

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to bottom (no relations).

\*******************************************************************/
void variable_sensitivity_domaint::make_bottom()
{
  abstract_state.make_bottom();
  return;
}

/*******************************************************************\

Function: variable_sensitivity_domaint::make_top

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to top (all relations).

\*******************************************************************/
void variable_sensitivity_domaint::make_top()
{
  abstract_state.make_top();
}


/*******************************************************************\

Function: variable_sensitivity_domaint::make_entry

  Inputs: None

 Outputs: None

 Purpose: Set up a sane entry state.

\*******************************************************************/
void variable_sensitivity_domaint::make_entry()
{
  abstract_state.make_top();
}

/*******************************************************************\

Function: variable_sensitivity_domaint::merge

  Inputs: The other domain (b) and it's preceding location (from) and
          current location (to).

 Outputs: True if something has changed.

 Purpose: Computes the join between "this" and "b".

\*******************************************************************/

bool variable_sensitivity_domaint::merge(
  const variable_sensitivity_domaint &b,
  locationt from,
  locationt to)
{
  #ifdef DEBUG
  std::cout << "Merging from/to:\n "
            << from->location_number << " --> "
            << to->location_number << std::endl;
  #endif

  // Use the abstract_environment merge
  bool any_changes=abstract_state.merge(b.abstract_state);
  return any_changes;
}

/*******************************************************************\

Function: variable_sensitivity_domaint::ai_simplify

  Inputs:
   condition - the expression to simplify
   ns - the namespace
   lhs - is the expression on the left hand side

 Outputs: True if simplified the condition. False otherwise. condition
          will be updated with the simplified condition if it has worked

 Purpose: Use the information in the domain to simplify the expression
          with respect to the current location.  This may be able to
          reduce some values to constants.

\*******************************************************************/

bool variable_sensitivity_domaint::ai_simplify(
  exprt &condition, const namespacet &ns, const bool lhs) const
{
  if (lhs)
    return false;
  else
  {
    sharing_ptrt<abstract_objectt> res = abstract_state.eval(condition, ns);
    exprt c = res->to_constant();

    if (c.id() == ID_nil)
      return false;
    else
    {
      bool b = (condition!=c);
      condition = c;
      return b;
    }
  }
}

bool variable_sensitivity_domaint::is_bottom() const
{
  return abstract_state.get_is_bottom();
}

bool variable_sensitivity_domaint::is_top() const
{
  return abstract_state.get_is_top();
}
