/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/


#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/ai.h>
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
  value=nil_exprt();
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
  value=nil_exprt();
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
    //address_of_exprt address_expr(to_address_of_expr(e));
    value=e;
    top=false;
  }
  else
  {
    if(e.id()==ID_constant)
    {
      constant_exprt constant_expr(to_constant_expr(e));
      if(constant_expr.get_value()==ID_NULL)
      {
        value=e;
        top=false;
      }
      else
      {
        // TODO(tkiley): These should probably be logged.
        // unknown type
        value=nil_exprt();
      }
    }
    else
    {
      value=nil_exprt();
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::merge_state

  Inputs:
   op1 - the first pointer abstract object
   op2 - the second pointer abstract object

 Outputs: Returns true if this changed from op1

 Purpose: Set this abstract object to be the result of merging two
          other abstract objects. This handles the case where if they are
          both pointing to the same object we keep the value.

\*******************************************************************/

bool constant_pointer_abstract_objectt::merge_state(
  const constant_pointer_abstract_pointert op1,
  const constant_pointer_abstract_pointert op2)
{
  bool parent_merge_change=abstract_objectt::merge_state(op1, op2);
  if(top || bottom)
  {
    return parent_merge_change;
  }
  else
  {
    if(op1->value==op2->value)
    {
      value=op1->value;
      return false;
    }
    else
    {
      top=true;
      value=nil_exprt();
      assert(!bottom);
      return !op1->top;
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
    // TODO(tkiley): I think we would like to eval this before using it
    // in the to_constant.
    return value;
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
    if(value.id()==ID_constant && value.get(ID_value)==ID_NULL)
    {
      out << "NULL";
    }
    else
    {
      out << "ptr ->(";
      if(value.id()==ID_address_of)
      {
        const address_of_exprt &address_expr(to_address_of_expr(value));
        if(address_expr.object().id()==ID_symbol)
        {
          const symbol_exprt &symbol_pointed_to(
            to_symbol_expr(address_expr.object()));

          out << symbol_pointed_to.get_identifier();
        }
      }

      out << ")";
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::read_dereference

  Inputs:
   env - the environment
   ns - the namespace

 Outputs: An abstract object representing the value this pointer is pointing
          to

 Purpose: A helper function to dereference a value from a pointer. Providing
          the pointer can only be pointing at one thing, returns an abstract
          object representing that thing. If null or top will return top.

\*******************************************************************/

abstract_object_pointert constant_pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env, const namespacet &ns) const
{
  if(top || bottom || value.id()==ID_nil)
  {
    // Return top if dereferencing a null pointer or we are top
    bool is_value_top = top || value.id()==ID_nil;
    return env.abstract_object_factory(
      type.subtype(), ns, is_value_top, !is_value_top);
  }
  else
  {
    if(value.id()==ID_address_of)
    {
      return env.eval(value.op0(), ns);
    }
    else if(value.id()==ID_constant)
    {
      // Reading a null pointer, return top
      return env.abstract_object_factory(type.subtype(), ns, true, false);
    }
    else
    {
      return env.abstract_object_factory(type.subtype(), ns, true, false);
    }
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::write_dereference

  Inputs:
   environment - the environment
   ns - the namespace
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
    const namespacet &ns,
    const std::stack<exprt> stack,
    const abstract_object_pointert new_value,
    bool merging_write)
{
  if(top || bottom)
  {
    return pointer_abstract_objectt::write_dereference(
      environment, ns, stack, new_value, merging_write);
  }
  else
  {
    if(stack.empty())
    {
      sharing_ptrt<constant_pointer_abstract_objectt> copy=
        sharing_ptrt<constant_pointer_abstract_objectt>(
          new constant_pointer_abstract_objectt(*this));

      if(merging_write)
      {
        abstract_object_pointert pointed_value=environment.eval(value, ns);
        bool modifications;
        pointed_value->merge(new_value, modifications);
      }
      else
      {
        environment.assign(value, new_value, ns);
      }
      return copy;
    }
    else
    {
      abstract_object_pointert pointed_value=environment.eval(value, ns);
      return std::dynamic_pointer_cast<constant_pointer_abstract_objectt>(
        environment.write(pointed_value, new_value, stack, ns, merging_write));
    }
  }
}
