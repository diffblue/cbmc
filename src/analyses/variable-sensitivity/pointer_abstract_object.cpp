/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <util/std_types.h>
#include <util/std_expr.h>

#include <analyses/variable-sensitivity/abstract_enviroment.h>

#include "pointer_abstract_object.h"


/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(const typet &t):
  abstract_objectt(t)
{
  assert(t.id()==ID_pointer);
}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(
  const typet &t, bool tp, bool bttm):
    abstract_objectt(t, tp, bttm)
{
  assert(t.id()==ID_pointer);
}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(
  const pointer_abstract_objectt &old):
    abstract_objectt(old)
{}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(const exprt &e):
    abstract_objectt(e)
{
  assert(e.type().id()==ID_pointer);
}

/*******************************************************************\

Function: array_abstract_objectt::read_index

  Inputs:
   env - the environment
   index - the expression used to access the specific value in the array

 Outputs: An abstract object representing the value in the array

 Purpose: A helper function to read elements from an array. More precise
          abstractions may override this to provide more precise results.

\*******************************************************************/

abstract_object_pointert pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env) const
{
  pointer_typet pointer_type(to_pointer_type(type));
  const typet &pointed_to_type=pointer_type.subtype();

  return env.abstract_object_factory(pointed_to_type, true, false);
}

/*******************************************************************\

Function: abstract_object_pointert array_abstract_objectt

  Inputs:
   environment - the abstract environment
   stack - the remaining stack of expressions on the LHS to evaluate
   index_expr - the expression uses to access a specific index
   value - the value we are trying to assign to that value in the array
   merging_write - ?

 Outputs: The struct_abstract_objectt representing the result of writing
          to a specific component. In this case this will always be top
          as we are not tracking the value of this struct.

 Purpose: A helper function to evaluate writing to a component of a struct.
          More precise abstractions may override this to
          update what they are storing for a specific component.

\*******************************************************************/

sharing_ptrt<pointer_abstract_objectt> pointer_abstract_objectt::write_dereference(
  abstract_environmentt &environment,
  const std::stack<exprt> stack,
  const abstract_object_pointert value,
  bool merging_write)
{
  if(is_top())
  {
    environment.havoc("Writing to a 2value pointer");
    return sharing_ptrt<pointer_abstract_objectt>(
      new pointer_abstract_objectt(*this));
  }
  else
  {
    sharing_ptrt<pointer_abstract_objectt> copy(
      new pointer_abstract_objectt(*this));
    copy->top=false;
    copy->bottom=true;
    return copy;
  }
}
