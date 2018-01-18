/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <ostream>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "constant_array_abstract_object.h"

/*******************************************************************\

Function: constant_array_abstract_objectt::constant_array_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

constant_array_abstract_objectt::constant_array_abstract_objectt(typet type):
array_abstract_objectt(type)
{}

/*******************************************************************\

Function: constant_array_abstract_objectt::constant_array_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

constant_array_abstract_objectt::constant_array_abstract_objectt(
  typet type, bool top, bool bottom):
array_abstract_objectt(type, top, bottom)
{}

/*******************************************************************\

Function: constant_array_abstract_objectt::constant_array_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object
   environment - the environment the abstract object is being created in
   ns - the namespace

 Outputs:

 Purpose:

\*******************************************************************/

constant_array_abstract_objectt::constant_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns):
    array_abstract_objectt(expr, environment, ns)
{
  if(expr.id()==ID_array)
  {
    int index=0;
    for(const exprt &entry : expr.operands())
    {
      map[mp_integer(index)]=environment.eval(entry, ns);
      ++index;
    }
    clear_top();
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::merge

  Inputs:
   other - The object to merge in

 Outputs: Returns the result of the merge.

 Purpose: Tries to do an array/array merge if merging with a constant array
          If it can't, falls back to parent merge

\*******************************************************************/

abstract_object_pointert constant_array_abstract_objectt::merge(
  abstract_object_pointert other) const
{
  auto cast_other=
    std::dynamic_pointer_cast<const constant_array_abstract_objectt>(other);
  if(cast_other)
  {
    return constant_array_merge(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return array_abstract_objectt::merge(other);
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::constant_array_merge

  Inputs:
   other - The object to merge in

 Outputs: Returns a new abstract object that is the result of the merge
          unless the merge is the same as this abstract object, in which
          case it returns this..

 Purpose: Merges an array into this array

\*******************************************************************/

abstract_object_pointert constant_array_abstract_objectt::constant_array_merge(
  const constant_array_pointert other) const
{
  if(is_bottom())
  {
    return std::make_shared<constant_array_abstract_objectt>(*other);
  }
  else
  {
    array_mapt merged_map=array_mapt();
    bool modified=
      abstract_objectt::merge_maps<mp_integer>(map, other->map, merged_map);
    if(!modified)
    {
      return shared_from_this();
    }
    else
    {
      const auto &result=
        std::dynamic_pointer_cast<constant_array_abstract_objectt>(
          mutable_clone());

      result->map=merged_map;

      assert(!result->is_top());
      assert(!result->is_bottom());
      return result;
    }
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::output

  Inputs:
   out - the stream to write to
   ai - the abstract interpreter that contains the abstract domain
        (that contains the object ... )
   ns - the current namespace

 Outputs:

 Purpose: To provide a human readable string to the out representing
          the current known value about this object. For this array we
          print: { [0] - <output of object at index 0... }

\*******************************************************************/

void constant_array_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(is_top() || is_bottom())
  {
    array_abstract_objectt::output(out, ai, ns);
  }
  else
  {
    out << "{";
    for(const auto &entry : map)
    {
      out << "[" << entry.first << "] = ";
      entry.second->output(out, ai, ns);

      // Start outputting specific last_written_locations
      out << " @ ";
      output_last_written_locations(out,
          entry.second->get_last_written_locations());

      out << "\n";
    }
    out << "}";
  }
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
abstract_object_pointert constant_array_abstract_objectt::read(
  const abstract_environmentt &env,
  const exprt &specifier,
  const namespacet &ns) const
{
  return read_index(env, to_index_expr(specifier), ns);
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
abstract_object_pointert constant_array_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> stack,
  const exprt &specifier,
  const abstract_object_pointert value,
  bool merging_write) const
{
  return write_index(
    environment, ns, stack, to_index_expr(specifier), value,
    merging_write);
}

/*******************************************************************\

Function: constant_array_abstract_objectt::read_index

  Inputs:
   env - the environment
   index - the expression used to access the specific value in the array

 Outputs: An abstract object representing the value in the array

 Purpose: A helper function to read elements from an array. This will return
          the abstract object stored for that index, or top if we don't know
          about the specified index.
          If we can't resolve the index to a constant, we return top

\*******************************************************************/

abstract_object_pointert constant_array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet &ns) const
{
  if(is_top())
  {
    return env.abstract_object_factory(
      index.type(), ns, true);
  }
  else
  {
    assert(!is_bottom());
    mp_integer index_value;
    if(eval_index(index, env, ns, index_value))
    {
      // Here we are assuming it is always in bounds
      if(map.find(index_value)==map.cend())
      {
        return env.abstract_object_factory(type().subtype(), ns, true, false);
      }
      else
      {
        return map.find(index_value)->second;
      }
    }
    else
    {
      // Reading from somewhere in the array
      // TODO(tkiley): merge all the values of the array, we may be able to
      // do better than returning top
      return env.abstract_object_factory(type().subtype(), ns, true, false);
    }
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::write_index

  Inputs:
   environment - the abstract environment
   ns - the namespace
   stack - the remaining stack of expressions on the LHS to evaluate
   index_expr - the expression uses to access a specific index
   value - the value we are trying to assign to that value in the array
   merging_write - Should this and all future writes be merged with the current
                   value

 Outputs: The array_abstract_objectt representing the result of writing
          to a specific index.

 Purpose: A helper function to evaluate writing to a index of an array.

\*******************************************************************/

sharing_ptrt<array_abstract_objectt>
  constant_array_abstract_objectt::write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const index_exprt &index_expr,
    const abstract_object_pointert value,
    bool merging_write) const
{
  if(is_bottom())
  {
    return array_abstract_objectt::write_index(
      environment, ns, stack, index_expr, value, merging_write);
  }
  else
  {
    if(stack.empty())
    {
      auto copy=
        internal_sharing_ptrt<constant_array_abstract_objectt>(
          new constant_array_abstract_objectt(*this));

      mp_integer index_value;
      if(!merging_write && eval_index(index_expr, environment, ns, index_value))
      {
        if(is_top())
        {
          copy->clear_top();
        }

        copy->map[index_value]=value;
        return copy;
      }
      else
      {
        // try to write to all
        // TODO(tkiley): Merge with each entry
        return array_abstract_objectt::write_index(
          environment, ns, stack, index_expr, value, merging_write);
      }
    }
    else
    {
      auto copy=
        internal_sharing_ptrt<constant_array_abstract_objectt>(
          new constant_array_abstract_objectt(*this));

      mp_integer index_value;
      if(eval_index(index_expr, environment, ns, index_value))
      {
        // Here we assume the write is in bounds
        abstract_object_pointert array_entry;
        if(map.find(index_value)!=map.cend())
        {
          array_entry=map.at(index_value);
        }
        else
        {
          array_entry=get_top_entry(environment, ns);
        }

        if(is_top())
        {
          copy->clear_top();
        }
        copy->map[index_value]=environment.write(
          array_entry, value, stack, ns, merging_write);

        return copy;
      }
      else
      {
        for(const auto &array_entry : map)
        {
          // Merging write since we don't know which index we are writing to
          copy->map[array_entry.first]=
            environment.write(
              array_entry.second, value, stack, ns, true);
          if(is_top())
          {
            copy->clear_top();
          }
        }

        return copy;
      }
    }
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::get_top_entry

  Inputs:
   environment - the abstract environment
   ns - the namespace

 Outputs: An abstract object pointer of type type().subtype() (i.e. the
          type of the array's values).

 Purpose: Short hand method for creating a top element of the array

\*******************************************************************/

abstract_object_pointert constant_array_abstract_objectt::get_top_entry(
  const abstract_environmentt &env, const namespacet &ns) const
{
  return env.abstract_object_factory(type().subtype(), ns, true, false);
}

/*******************************************************************\

Function: constant_array_abstract_objectt::eval_index

  Inputs:
   environment - the abstract environment
   ns - the namespace

 Outputs: An abstract object pointer of type type().subtype() (i.e. the
          type of the array's values).

 Purpose: Short hand method for creating a top element of the array

\*******************************************************************/

bool constant_array_abstract_objectt::eval_index(
  const index_exprt &index,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index) const
{
  abstract_object_pointert index_abstract_object=env.eval(index.index(), ns);
  exprt value=index_abstract_object->to_constant();
  if(value.is_constant())
  {
    constant_exprt constant_index=to_constant_expr(value);
    bool result=to_integer(constant_index, out_index);
    return !result;
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: constant_array_abstract_objectt::update_sub_elements

  Inputs:
   locations - Locations to write

 Outputs: None

 Purpose: Updates write location for sub-elements.

          For example, if a[2] = {5, 6}, this will update
          the write location for objects 5 and 6 as well as a.

\*******************************************************************/

void constant_array_abstract_objectt::update_sub_elements(
    const locationst &locations)
{
  for(auto &item: map)
  {
    item.second=item.second->update_last_written_locations(locations, true);
  }
}
