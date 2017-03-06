/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include "array_abstract_object.h"


/*******************************************************************\

Function: array_abstract_objectt::array_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

array_abstract_objectt::array_abstract_objectt(const typet &t):
  abstract_objectt(t)
{
  assert(t.id()==ID_array);
}

/*******************************************************************\

Function: array_abstract_objectt::array_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

array_abstract_objectt::array_abstract_objectt(
  const typet &t, bool tp, bool bttm):
    abstract_objectt(t, tp, bttm)
{
  assert(t.id()==ID_array);
}

/*******************************************************************\

Function: array_abstract_objectt::array_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

array_abstract_objectt::array_abstract_objectt(
  const array_abstract_objectt &old):
    abstract_objectt(old)
{}

/*******************************************************************\

Function: array_abstract_objectt::array_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

array_abstract_objectt::array_abstract_objectt(const exprt &e):
  abstract_objectt(e)
{
  assert(e.type().id()==ID_array);
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

abstract_object_pointert array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet& ns) const
{
  array_typet array_type(to_array_type(type()));
  const typet &subtype=array_type.subtype();

  // if we are bottom then so are the values in the array
  // otherwise the values are top
  return env.abstract_object_factory(subtype, ns, !is_bottom(), is_bottom());
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

sharing_ptrt<array_abstract_objectt> array_abstract_objectt::write_index(
  abstract_environmentt &environment,
  const std::stack<exprt> stack,
  const index_exprt &index_expr,
  const abstract_object_pointert value,
  bool merging_write)
{
  // TODO(tkiley): Should this in fact havoc since we can't verify
  // that we are not writing past the end of the array - Martin said
  // default should be not to, but perhaps for soundness the base class should
  // havoc and the default should derive from this.
  if(is_top())
  {
    return sharing_ptrt<array_abstract_objectt>(
      new array_abstract_objectt(*this));
  }
  else
  {
    sharing_ptrt<array_abstract_objectt> copy(
      new array_abstract_objectt(*this));
    copy->top=false;
    copy->bottom=true;
    return copy;
  }
}
