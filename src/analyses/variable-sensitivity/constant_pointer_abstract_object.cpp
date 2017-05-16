/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

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
  const typet &t):
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
  const typet &t, bool tp, bool bttm):
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
  const abstract_environmentt &environment,
  const namespacet &ns):
    pointer_abstract_objectt(e, environment, ns)
{
  assert(e.type().id()==ID_pointer);
  value=nil_exprt();

  if(e.id()==ID_address_of)
  {
    value=e;
    top=false;
  }
  else if(e.id()==ID_constant)
  {
    constant_exprt constant_expr(to_constant_expr(e));
    if(constant_expr.get_value()==ID_NULL)
    {
      value=e;
      top=false;
    }
  }
  // Else unknown expression type - possibly we should handle more
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::merge

  Inputs:
   other - the pointer being merged

 Outputs: Returns the result of the merge.

 Purpose: Set this abstract object to be the result of merging this
          abstract object. This calls the merge_constant_pointers if
          we are trying to merge a constant pointer we use the constant pointer
          constant pointer merge

\*******************************************************************/

const abstract_objectt *constant_pointer_abstract_objectt::merge(
  abstract_object_pointert other) const
{
  auto cast_other=
    std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other);
  if(cast_other)
  {
    return merge_constant_pointers(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish?
    return pointer_abstract_objectt::merge(other);
  }
}

/*******************************************************************\

Function: constant_pointer_abstract_objectt::merge_constant_pointers

  Inputs:
   other - the pointer being merged

 Outputs: Returns a new abstract object that is the result of the merge
          unless the merge is the same as this abstract object, in which
          case it returns this.

 Purpose: Merges two constant pointers. If they are pointing at the same
          value, we merge, otherwise we set to top.

\*******************************************************************/

const abstract_objectt *constant_pointer_abstract_objectt::merge_constant_pointers(
  const constant_pointer_abstract_pointert other) const
{
  const abstract_objectt *parent_merge=pointer_abstract_objectt::merge(other);

  // Did the parent merge result in a definitive result
  if(!parent_merge->is_top() && !parent_merge->is_bottom())
  {
    if(value==other->value)
    {
      // If the parent merge changed the merge, but we're neither top nor bottom
      // then we can still return this
      if(parent_merge!=this)
      {
        delete parent_merge;
        parent_merge=nullptr;
      }
      return this;
    }
    else
    {
      // We need to make a new clone since the one created by the parent
      // merge is immutable
      if(parent_merge!=this)
      {
        delete parent_merge;
      }

      constant_pointer_abstract_objectt *result=
        static_cast<constant_pointer_abstract_objectt *>(mutable_clone());

      result->make_top();
      assert(!result->is_bottom());
      result->value=exprt();
      return result;
    }
  }
  else
  {
    return parent_merge;
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
  if(is_top() || is_bottom())
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
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(is_top() || is_bottom())
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
  if(is_top() || is_bottom() || value.id()==ID_nil)
  {
    // Return top if dereferencing a null pointer or we are top
    bool is_value_top = is_top() || value.id()==ID_nil;
    return env.abstract_object_factory(
      type().subtype(), ns, is_value_top, !is_value_top);
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
      return env.abstract_object_factory(type().subtype(), ns, true, false);
    }
    else
    {
      return env.abstract_object_factory(type().subtype(), ns, true, false);
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
    bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    return pointer_abstract_objectt::write_dereference(
      environment, ns, stack, new_value, merging_write);
  }
  else
  {
    // If not an address, we don't know what we are pointing to
    if(value.id()!=ID_address_of)
    {
      return pointer_abstract_objectt::write_dereference(
        environment, ns, stack, new_value, merging_write);
    }

    const address_of_exprt &address_expr=to_address_of_expr(value);

    sharing_ptrt<constant_pointer_abstract_objectt> copy=
      sharing_ptrt<constant_pointer_abstract_objectt>(
        new constant_pointer_abstract_objectt(*this));

    if(stack.empty())
    {
      // We should not be changing the type of an abstract object
      assert(new_value->type()==type().subtype());


      if(merging_write)
      {
        abstract_object_pointert pointed_value=
          environment.eval(address_expr.object(), ns);
        bool modifications;
        abstract_object_pointert merged_value=
          abstract_objectt::merge(pointed_value, new_value, modifications);
        environment.assign(address_expr.object(), merged_value, ns);
      }
      else
      {
        environment.assign(address_expr.object(), new_value, ns);
      }
    }
    else
    {
      abstract_object_pointert pointed_value=
        environment.eval(address_expr.object(), ns);
      environment.write(pointed_value, new_value, stack, ns, merging_write);

      // but the pointer itself does not change!
    }
    return copy;
  }
}
