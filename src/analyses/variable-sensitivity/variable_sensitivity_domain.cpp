/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

\*******************************************************************/

#include <ostream>

#include <util/message.h>
#include <util/simplify_expr.h>

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
      if(1) // (flow_sensitivity == FLOW_SENSITIVE)
      {
        // Get the next line
        locationt next=from;
        next++;
        // Is this a GOTO to the next line (i.e. pointless)
        if(next!=from->get_target())
        {
          if(to==from->get_target())
          {
            // The AI is exploring the branch where the jump is taken
            abstract_state.assume(instruction.guard, ns);
          }
          else
          {
            // Exploring the path where the jump is not taken - therefore assume
            // the condition is false
            abstract_state.assume(not_exprt(instruction.guard), ns);
          }
        }
        // ignore jumps to the next line, we can assume nothing
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

  assert(abstract_state.verify());
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

  assert(abstract_state.verify());
  return any_changes;
}

/*******************************************************************\

Function: variable_sensitivity_domaint::ai_simplify

  Inputs:
   condition - the expression to simplify
   ns - the namespace
   lhs - is the expression on the left hand side

 Outputs: True if no simplification was made

 Purpose: Use the information in the domain to simplify the expression
          with respect to the current location.  This may be able to
          reduce some values to constants.

\*******************************************************************/

bool variable_sensitivity_domaint::ai_simplify(
  exprt &condition, const namespacet &ns) const
{
  sharing_ptrt<abstract_objectt> res=abstract_state.eval(condition, ns);
  exprt c=res->to_constant();

  if(c.id()==ID_nil)
  {
    bool no_simplification=true;

    // Try to simplify recursively any child operations
    for(exprt &op : condition.operands())
    {
      no_simplification&=ai_simplify(op, ns);
    }

    return no_simplification;
  }
  else
  {
    bool condition_changed=(condition!=c);
    condition=c;
    return !condition_changed;
  }
}

/*******************************************************************\

Function: variable_sensitivity_domaint::is_bottom

  Inputs:

 Outputs: True if the domain is bottom (i.e. unreachable).

 Purpose: Find out if the domain is currently unreachable.

\*******************************************************************/

bool variable_sensitivity_domaint::is_bottom() const
{
  return abstract_state.is_bottom();
}

/*******************************************************************\

Function: variable_sensitivity_domaint::is_top

  Inputs:

 Outputs: True if the domain is top

 Purpose: Is the domain completely top at this state

\*******************************************************************/
bool variable_sensitivity_domaint::is_top() const
{
  return abstract_state.is_top();
}

/*******************************************************************\

Function: variable_sensitivity_domaint::ai_simplify_lhs

  Inputs:
   condition - the expression to simplify
   ns - the namespace

 Outputs: True if condition did not change. False otherwise. condition
          will be updated with the simplified condition if it has worked

 Purpose: Use the information in the domain to simplify the expression
          on the LHS of an assignment. This for example won't simplify symbols
          to their values, but does simplify indices in arrays, members of
          structs and dereferencing of pointers

\*******************************************************************/

bool variable_sensitivity_domaint::ai_simplify_lhs(
  exprt &condition, const namespacet &ns) const
{
  // Care must be taken here to give something that is still writable
  if(condition.id()==ID_index)
  {
    index_exprt ie = to_index_expr(condition);
    exprt index = ie.index();
    bool changed = ai_simplify(index, ns);
    if(changed)
    {
      ie.index() = index;
      condition = simplify_expr(ie, ns);
    }

    return !changed;
  }
  else if(condition.id()==ID_dereference)
  {
    dereference_exprt de = to_dereference_expr(condition);
    exprt pointer = de.pointer();
    bool changed = ai_simplify(pointer, ns);
    if(changed)
    {
      de.pointer() = pointer;
      condition = simplify_expr(de, ns);  // So *(&x) -> x
    }

    return !changed;
  }
  else if(condition.id()==ID_member)
  {
    member_exprt me = to_member_expr(condition);
    exprt compound = me.compound();
    // Carry on the RHS since we still require an addressable object for the
    // struct
    bool changed = ai_simplify_lhs(compound, ns);
    if(changed)
    {
      me.compound() = compound;
      condition = simplify_expr(me, ns);
    }

    return !changed;
  }
  else
    return true;
}
