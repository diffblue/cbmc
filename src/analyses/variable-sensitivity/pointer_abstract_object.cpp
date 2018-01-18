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

/**
 * A helper function to evaluate an abstract object contained
 * within a container object. More precise abstractions may override this
 * to return more precise results.
 *
 * \param env the abstract environment
 * \param specifier a modifier expression, such as an array index or field
 * specifier used to indicate access to a specific component
 * \param ns the current namespace
 *
 * \return the abstract_objectt representing the value of the read component.
 */
abstract_object_pointert pointer_abstract_objectt::read(
  const abstract_environmentt &env,
  const exprt &specifier,
  const namespacet &ns) const
{
  return read_dereference(env, ns);
}

/**
 * A helper function to evaluate writing to a component of an
 * abstract object. More precise abstractions may override this to
 * update what they are storing for a specific component.
 *
 * \param environment the abstract environment
 * \param ns the current namespace
 * \param stack the remaining stack of expressions on the LHS to evaluate
 * \param specifier the expression uses to access a specific component
 * \param value the value we are trying to write to the component
 * \param merging_write if true, this and all future writes will be merged
 * with the current value
 *
 * \return the abstract_objectt representing the result of writing
 * to a specific component.
 */
abstract_object_pointert pointer_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> stack,
  const exprt &specifier,
  const abstract_object_pointert value,
  bool merging_write) const
{
  return write_dereference(environment, ns, stack, value, merging_write);
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
  if(is_top() || is_bottom())
  {
    environment.havoc("Writing to a 2value pointer");
    return std::dynamic_pointer_cast<const pointer_abstract_objectt>(clone());
  }
  else
  {
    return sharing_ptrt<pointer_abstract_objectt>(
      new pointer_abstract_objectt(type(), true, false));
  }
}
