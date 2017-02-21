/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

#include "struct_abstract_object.h"


/*******************************************************************\

Function: struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

struct_abstract_objectt::struct_abstract_objectt(const typet &t):
  abstract_objectt(t)
{
  assert(t.id()==ID_struct);
}

/*******************************************************************\

Function: struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

struct_abstract_objectt::struct_abstract_objectt(
  const typet &t, bool tp, bool bttm):
    abstract_objectt(t, tp, bttm)
{
  assert(t.id()==ID_struct);
}

/*******************************************************************\

Function: struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

struct_abstract_objectt::struct_abstract_objectt(
  const struct_abstract_objectt &old):
    abstract_objectt(old)
{}

/*******************************************************************\

Function: struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

struct_abstract_objectt::struct_abstract_objectt(const constant_exprt &e):
  abstract_objectt(e)
{
  assert(e.type().id()==ID_struct);
}

/*******************************************************************\

Function: struct_abstract_objectt::read_component

  Inputs:
   environment - the abstract environment
   member_expr - the expression uses to access a specific component

 Outputs: The abstract object representing the value of that component. For
          this abstraction this will always be top since we are not tracking
          the struct.

 Purpose: A helper function to evaluate the abstract object contained
          within a struct. More precise abstractions may override this
          to return more precise results.

\*******************************************************************/

abstract_object_pointert struct_abstract_objectt::read_component(
  const abstract_environmentt &environment, const member_exprt &member_expr)
{
  // Presumably reading from a bottom struct is bad?
  assert(!bottom);
  return environment.abstract_object_factory(member_expr.type(), true);
}

/*******************************************************************\

Function: struct_abstract_objectt::write_component

  Inputs:
   environment - the abstract environment
   stack - the remaining stack of expressions on the LHS to evaluate
   member_expr - the expression uses to access a specific component

 Outputs: The struct_abstract_objectt representing the result of writing
          to a specific component. In this case this will always be top
          as we are not tracking the value of this struct.

 Purpose: A helper function to evaluate writing to a component of a struct.
          More precise abstractions may override this to
          update what they are storing for a specific component.

\*******************************************************************/

sharing_ptrt<struct_abstract_objectt> struct_abstract_objectt::write_component(
  const abstract_environmentt &environment,
  const std::stack<exprt> stack,
  const member_exprt &member_expr)
{
  // Return a copy of this set to top
  sharing_ptrt<struct_abstract_objectt> copy(
    new struct_abstract_objectt(*this));
  copy->top=true;
  copy->bottom=false;
  return copy;
}
