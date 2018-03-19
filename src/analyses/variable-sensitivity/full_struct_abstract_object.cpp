/*******************************************************************\

Module: Struct abstract object

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

#include "full_struct_abstract_object.h"

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/**
 * \brief Explicit copy-constructor to make it clear that the shared_map
 *        used to store the values of fields is copy-constructed as well
 *        to ensure it shares as much data as possible.
 */
full_struct_abstract_objectt::full_struct_abstract_objectt(
  const full_struct_abstract_objectt &ao):
    struct_abstract_objectt(ao), map(ao.map)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

/*******************************************************************\

Function: full_struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

full_struct_abstract_objectt::full_struct_abstract_objectt(const typet &t):
  struct_abstract_objectt(t)
{
  PRECONDITION(t.id()==ID_struct);
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

/*******************************************************************\

Function: struct_abstract_objectt::struct_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or
          neither asserts if both top and bottom are true

\*******************************************************************/

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const typet &t, bool top, bool bottom):
    struct_abstract_objectt(t, top, bottom)
{
  PRECONDITION(t.id()==ID_struct);
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

/*******************************************************************\

Function: full_struct_abstract_objectt::full_struct_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an
          abstract object

 Outputs:

 Purpose:

\*******************************************************************/

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns):
    struct_abstract_objectt(e, environment, ns)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

/*******************************************************************\

Function: struct_abstract_objectt::read_component

  Inputs:
   environment - the abstract environment
   member_expr - the expression uses to access a specific component

 Outputs: The abstract object representing the value of that
          component. For this abstraction this will always be top
          since we are not tracking the struct.

 Purpose: A helper function to evaluate the abstract object contained
          within a struct. More precise abstractions may override
          this to return more precise results.

\*******************************************************************/

abstract_object_pointert full_struct_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const member_exprt &member_expr,
  const namespacet& ns) const
{
#ifdef DEBUG
  std::cout << "Reading component " << member_expr.get_component_name()
            << std::endl;
#endif

  if(is_top())
  {
    return environment.abstract_object_factory(
      member_expr.type(), ns, true);
  }
  else
  {
    PRECONDITION(!is_bottom());

    const irep_idt c=member_expr.get_component_name();

    shared_struct_mapt::const_find_type value=map.find(c);

    if(value.second)
    {
      return value.first;
    }
    else
    {
      return environment.abstract_object_factory(
        member_expr.type(), ns, true);
    }
  }
}

/*******************************************************************\

Function: struct_abstract_objectt::write_component

  Inputs:
   environment - the abstract environment
   stack - the remaining stack of expressions on the LHS to evaluate
   member_expr - the expression uses to access a specific component
   value - the value we are trying to write to the component

 Outputs: The struct_abstract_objectt representing the result of
          writing to a specific component. In this case this will
          always be top as we are not tracking the value of this
          struct.

 Purpose: A helper function to evaluate writing to a component of a
          struct. More precise abstractions may override this to
          update what they are storing for a specific component.

\*******************************************************************/

sharing_ptrt<struct_abstract_objectt>
  full_struct_abstract_objectt::write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const member_exprt &member_expr,
    const abstract_object_pointert value,
    bool merging_write) const
{
#ifdef DEBUG
  std::cout << "Writing component " << member_expr.get_component_name()
            << std::endl;
#endif

  if(is_bottom())
  {
    return sharing_ptrt<full_struct_abstract_objectt>(
      new full_struct_abstract_objectt(
        member_expr.compound().type(), false, true));
  }

  const auto &result=
    std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

  if(!stack.empty())
  {
    abstract_object_pointert starting_value;
    const irep_idt c=member_expr.get_component_name();
    shared_struct_mapt::const_find_type old_value = map.find(c);
    if(!old_value.second)
    {
      starting_value=
        environment.abstract_object_factory(
          member_expr.type(), ns, true, false);
    }
    else
    {
      starting_value=old_value.first;
    }

    result->map[c] =
      environment.write(starting_value, value, stack, ns, merging_write);

    result->clear_top();
    DATA_INVARIANT(result->verify(), "Structural invariants maintained");
    return result;
  }
  else
  {

#ifdef DEBUG
    std::cout << "Setting component" << std::endl;
#endif

    const irep_idt c=member_expr.get_component_name();

    if(merging_write)
    {
      if(is_top()) // struct is top
      {
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }

      INVARIANT(!result->map.empty(), "If not top, map cannot be empty");

      shared_struct_mapt::const_find_type old_value=result->map.find(c);

      if(!old_value.second) // component is top
      {
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }

      bool dummy;

      result->map[c] = abstract_objectt::merge(old_value.first, value, dummy);
    }
    else
    {
      result->map[c] = value;
      result->clear_top();
      INVARIANT(!result->is_bottom(), "top != bottom");
    }

    DATA_INVARIANT(result->verify(), "Structural invariants maintained");

    return result;
  }
}

/*******************************************************************\

Function: full_struct_abstract_objectt::output

  Inputs:
   out - the stream to write to
   ai - the abstract interpreter that contains the abstract domain
        (that contains the object ... )
   ns - the current namespace

 Outputs:

 Purpose: To provide a human readable string to the out representing
          the current known value about this object. For this array we
          print: { .component_name=<output of object for component_name... }

\*******************************************************************/

void full_struct_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  // To ensure that a consistent ordering of fields is output, use
  // the underlying type declaration for this struct to determine
  // the ordering
  struct_union_typet type_decl = to_struct_union_type(ns.follow(type()));

  bool first = true;

  out << "{";
  for(const auto field : type_decl.components())
  {
    auto value = map.find(field.get_name());
    if(value.second)
    {
      if(!first)
      {
        out << ", ";
      }
      out << '.' << field.get_name() << '=';
      value.first->output(out, ai, ns);
      first = false;
    }
  }
  out << "}";
}

/*******************************************************************\

Function: full_struct_abstract_objectt::verify

  Inputs:

 Outputs: Returns true if the struct is valid

 Purpose: To validate that the struct object is in a valid state.
          This means either it is top or bottom, or if neither of those
          then there exists something in the map of components.
          If there is something in the map, then it can't be top or bottom

\*******************************************************************/

bool full_struct_abstract_objectt::verify() const
{
  // Either the object is top or bottom (=> map empty)
  // or the map is not empty => neither top nor bottom
  return (is_top() || is_bottom()) == map.empty();
}

/*******************************************************************\

Function: full_struct_abstract_objectt::merge

  Inputs:
   other - the other object being merged

 Outputs: Returns the result of the merge.

 Purpose: To merge an abstract object into this abstract object. If
          the other is also a struct, we perform a constant_structs merge
          Otherwise we call back to the parent merge.

\*******************************************************************/

abstract_object_pointert full_struct_abstract_objectt::merge(
  abstract_object_pointert other) const
{
  constant_struct_pointert cast_other=
    std::dynamic_pointer_cast<const full_struct_abstract_objectt>(other);
  if(cast_other)
  {
    return merge_constant_structs(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return struct_abstract_objectt::merge(other);
  }
}

/*******************************************************************\

Function: full_struct_abstract_objectt::merge_constant_structs

  Inputs:
   other - the other object being merged

 Outputs: Returns a new abstract object that is the result of the merge
          unless the merge is the same as this abstract object, in which
          case it returns this.

 Purpose: Performs an element wise merge of the map for each struct

\*******************************************************************/

abstract_object_pointert full_struct_abstract_objectt::merge_constant_structs(
  constant_struct_pointert other) const
{
  if(is_bottom())
  {
    return std::make_shared<full_struct_abstract_objectt>(*other);
  }
  else
  {
    const auto &result=
      std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

    bool modified = abstract_objectt::merge_shared_maps<irep_idt>(
      map, other->map, result->map);

    if(!modified)
    {
      DATA_INVARIANT(verify(), "Structural invariants maintained");
      return shared_from_this();
    }
    else
    {
      INVARIANT(!result->is_top(), "Merge of maps will not generate top");
      INVARIANT(!result->is_bottom(), "Merge of maps will not generate bottom");
      DATA_INVARIANT(result->verify(), "Structural invariants maintained");
      return result;
    }
  }
}

/**
 * Apply a visitor operation to all sub elements of this abstract_object.
 * A sub element might be a member of a struct, or an element of an array,
 * for instance, but this is entirely determined by the particular
 * derived instance of abstract_objectt.
 *
 * \param visitor an instance of a visitor class that will be applied to
 * all sub elements
 * \return A new abstract_object if it's contents is modifed, or this if
 * no modification is needed
 */
abstract_object_pointert full_struct_abstract_objectt::visit_sub_elements(
  const abstract_object_visitort &visitor) const
{
  const auto &result=
    std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

  bool modified = false;

  shared_struct_mapt::viewt view;
  result->map.get_view(view);

  for(auto &item : view)
  {
    auto newval = visitor.visit(item.second);
    if(newval != item.second)
    {
      result->map[item.first] = newval;
      modified = true;
    }
  }

  if(modified)
  {
    return result;
  }
  else
  {
    return shared_from_this();
  }
}
