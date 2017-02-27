/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/


#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include "constant_pointer_abstract_object.h"

/*******************************************************************\

Function: constant_pointer_abstract_objectt::constant_pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &t, const abstract_environmentt &enviroment):
    pointer_abstract_objectt(t)
{
  assert(t.id()==ID_pointer);
  value=enviroment.abstract_object_factory(t.subtype(), true, false);
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::constant_pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const typet &t, bool tp, bool bttm, const abstract_environmentt &enviroment):
    pointer_abstract_objectt(t, tp, bttm)
{
  assert(t.id()==ID_pointer);
  value=enviroment.abstract_object_factory(t.subtype(), top, bottom);
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::constant_pointer_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const constant_pointer_abstract_objectt &old):
    pointer_abstract_objectt(old), value(old.value)
{}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::constant_pointer_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

constant_pointer_abstract_objectt::constant_pointer_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &enviroment,
  const namespacet &ns):
    pointer_abstract_objectt(e)
{
  assert(e.type().id()==ID_pointer);

  // TODO(tkiley): Should here really be handling the different ways we
  // can create a pointer
  if(e.id()==ID_address_of)
  {
    address_of_exprt address_expr(to_address_of_expr(e));
    value=enviroment.eval(address_expr.object(), ns);
    top=false;
  }
  else
  {
    if(e.id()==ID_constant)
    {
      constant_exprt constant_expr(to_constant_expr(e));
      if(constant_expr.get_value()==ID_NULL)
      {
        value=nullptr;
        top=false;
      }
      else
      {
        // TODO(tkiley): These should probably be logged.
        // unknown type
        value=enviroment.abstract_object_factory(type.subtype(), true, false);
      }
    }
    else
    {
      value=enviroment.abstract_object_factory(type.subtype(), true, false);
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::to_constant

  Inputs:

 Outputs: Returns an expression representing the value if it can.
          Returns a nil expression if it can be more than one value.
          Returns null_pointer expression if it must be null
          Returns an address_of_exprt with the value set to the
          result of to_constant called on whatever abstract object this
          pointer is pointing to.

 Purpose: To try and find a constant expression for this abstract object

\*******************************************************************/

exprt constant_pointer_abstract_objectt::to_constant() const
{
  if(top || bottom)
  {
    return pointer_abstract_objectt::to_constant();
  }
  else
  {
    if(value==nullptr)
    {
      return null_pointer_exprt(to_pointer_type(type));
    }
    else
    {
      const exprt &value_expr=value->to_constant();
      address_of_exprt address_expr(value_expr);
      return address_expr;
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::output

  Inputs:
   out - the stream to write to
   ai - ?
   ns - ?

 Outputs:

 Purpose: Print the value of the pointer. Either NULL if nullpointer or
          ptr -> ( output of what the pointer is pointing to).

\*******************************************************************/

void constant_pointer_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns)
{
  if(top || bottom)
  {
    pointer_abstract_objectt::output(out, ai, ns);
  }
  else
  {
    if(value==nullptr)
    {
      out << "NULL";
    }
    else
    {
      out << "ptr ->(";
      value->output(out, ai, ns);
      out << ")";
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::read_dereference

  Inputs:
   env - the environment

 Outputs: An abstract object representing the value this pointer is pointing
          to

 Purpose: A helper function to dereference a value from a pointer. Providing
          the pointer can only be pointing at one thing, returns an abstract
          object representing that thing. If null or top will return top.

\*******************************************************************/

abstract_object_pointert constant_pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env) const
{
  if(top || bottom || value==nullptr)
  {
    // Return top if dereferencing a null pointer or we are top
    bool is_value_top = top || value==nullptr;
    return env.abstract_object_factory(
      type.subtype(), is_value_top, !is_value_top);
  }
  else
  {
    return value;
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::write_dereference

  Inputs:
   environment - the environment
   stack - the remaining stack
   new_value - the value to write to the dereferenced pointer
   merging_write - is it a merging write (i.e. we aren't certain
                   we are writing to this particular pointer therefore
                   the value should be merged with whatever is already there
                   or we are certain we are writing to this pointer so
                   therefore the value can be replaced

 Outputs: A modified abstract object representing this pointer after it
          has been written to.

 Purpose: A helper function to evaluate writing to a pointers value.
          If the pointer can only be pointing to one element that it overwrites
          that element (or merges if merging_write) with the new value.
          If don't know what we are pointing to, we delegate to the parent.

\*******************************************************************/

sharing_ptrt<pointer_abstract_objectt>
  constant_pointer_abstract_objectt::write_dereference(
    abstract_environmentt &environment,
    const std::stack<exprt> stack,
    const abstract_object_pointert new_value,
    bool merging_write)
{
  if(top || bottom)
  {
    return pointer_abstract_objectt::write_dereference(
      environment, stack, new_value, merging_write);
  }
  else
  {
    // TODO(tkiley): support the stack
    assert(stack.empty());

    sharing_ptrt<constant_pointer_abstract_objectt> copy=
      sharing_ptrt<constant_pointer_abstract_objectt>(
        new constant_pointer_abstract_objectt(*this));

    // for
    // environment.assign()

    if(merging_write)
    {
      bool modifications;
      copy->value=value->merge(new_value, modifications);
    }
    else
    {
      copy->value=new_value;
    }
    return copy;
  }
}
