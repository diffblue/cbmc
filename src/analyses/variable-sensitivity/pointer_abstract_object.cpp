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

pointer_abstract_objectt::pointer_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns):
    abstract_objectt(e, environment, ns)
{
  assert(e.type().id()==ID_pointer);
}

/*******************************************************************\

Function: pointer_abstract_objectt::read_dereference

  Inputs:
   env - the environment
   ns - the namespace

 Outputs: An abstract object representing the value being pointed to

 Purpose: A helper function to read elements from an array. More precise
          abstractions may override this to provide more precise results.

\*******************************************************************/

abstract_object_pointert pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env, const namespacet &ns) const
{
  pointer_typet pointer_type(to_pointer_type(type()));
  const typet &pointed_to_type=pointer_type.subtype();

  return env.abstract_object_factory(pointed_to_type, ns, true, false);
}

/*******************************************************************\

Function: pointer_abstract_objectt::write_dereference

  Inputs:
   environment - the abstract environment
   ns - the namespace
   stack - the remaining stack of expressions on the LHS to evaluate
   value - the value we are trying to assign to what the pointer is
           pointing to
   merging_write - is it a merging write (i.e. we aren't certain
                   we are writing to this particular pointer therefore
                   the value should be merged with whatever is already there
                   or we are certain we are writing to this pointer so
                   therefore the value can be replaced

 Outputs: A modified abstract object representing this pointer after it
          has been written to.

 Purpose: A helper function to evaluate writing to a pointers value. More
          precise abstractions may override this provide more precise results.

\*******************************************************************/

sharing_ptrt<pointer_abstract_objectt>
  pointer_abstract_objectt::write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const abstract_object_pointert value,
    bool merging_write) const
{
  if(is_top())
  {
    environment.havoc("Writing to a 2value pointer");
    return sharing_ptrt<pointer_abstract_objectt>(
      new pointer_abstract_objectt(*this));
  }
  else
  {
    return sharing_ptrt<pointer_abstract_objectt>(
      new pointer_abstract_objectt(type(), false, true));
  }
}
