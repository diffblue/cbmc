/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/namespace.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

#include "union_abstract_object.h"


/*******************************************************************\

Function: union_abstract_objectt::union_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

union_abstract_objectt::union_abstract_objectt(const typet &type):
  abstract_objectt(type)
{
  assert(type.id()==ID_union);
}

/*******************************************************************\

Function: union_abstract_objectt::union_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

union_abstract_objectt::union_abstract_objectt(
  const typet &type, bool top, bool bottom):
    abstract_objectt(type, top, bottom)
{
  assert(type.id()==ID_union);
}

/*******************************************************************\

Function: union_abstract_objectt::union_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object
   environment - the environment the abstract object is going to be evaluated in.

 Outputs:

 Purpose:

\*******************************************************************/

union_abstract_objectt::union_abstract_objectt(
  const exprt &expr, const abstract_environmentt &environment,
  const namespacet &ns):
    abstract_objectt(expr, environment, ns)
{
  assert(ns.follow(expr.type()).id()==ID_union);
}

/*******************************************************************\

Function: union_abstract_objectt::read_component

  Inputs:
   environment - the abstract environment
   member_expr - the expression uses to access a specific component

 Outputs: The abstract object representing the value of that component. For
          this abstraction this will always be top since we are not tracking
          the union.

 Purpose: A helper function to evaluate the abstract object contained
          within a union. More precise abstractions may override this
          to return more precise results.

\*******************************************************************/

abstract_object_pointert union_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const member_exprt &member_expr,
  const namespacet &ns) const
{
  return environment.abstract_object_factory(
    member_expr.type(), ns, !is_bottom(), is_bottom());
}

/*******************************************************************\

Function: union_abstract_objectt::write_component

  Inputs:
   environment - the abstract environment
   stack - the remaining stack of expressions on the LHS to evaluate
   member_expr - the expression uses to access a specific component
   value - the value we are trying to write to the component

 Outputs: The union_abstract_objectt representing the result of writing
          to a specific component. In this case this will always be top
          as we are not tracking the value of this union.

 Purpose: A helper function to evaluate writing to a component of a union.
          More precise abstractions may override this to
          update what they are storing for a specific component.

\*******************************************************************/

sharing_ptrt<union_abstract_objectt> union_abstract_objectt::write_component(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const member_exprt &member_expr,
  const abstract_object_pointert value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    return std::dynamic_pointer_cast<const union_abstract_objectt>(clone());
  }
  else
  {
    return sharing_ptrt<union_abstract_objectt>(
      new union_abstract_objectt(type(), true, false));
  }
}
