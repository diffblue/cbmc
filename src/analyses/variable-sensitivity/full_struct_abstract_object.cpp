/*******************************************************************\

Module: Struct abstract object

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

#include "full_struct_abstract_object.h"

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

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
  assert(t.id()==ID_struct);
  assert(verify());
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
  assert(t.id()==ID_struct);
  assert(verify());
}

/*******************************************************************\

Function: full_struct_abstract_objectt::full_struct_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const full_struct_abstract_objectt &old):
    struct_abstract_objectt(old)
{
  map=old.map;
  assert(verify());
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
  assert(verify());
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
    assert(!is_bottom());

    irep_idt c=member_expr.get_component_name();

    struct_mapt::const_iterator it=map.find(c);

    if(it!=map.cend())
    {
      return it->second;
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

sharing_ptrt<struct_abstract_objectt> full_struct_abstract_objectt::write_component(
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

  // we only handle one level currently
  if(!stack.empty())
  {
    internal_sharing_ptrt<full_struct_abstract_objectt> copy(
      new full_struct_abstract_objectt(*this));

    abstract_object_pointert starting_value;
    irep_idt c=member_expr.get_component_name();
    if(map.find(c)==map.cend())
    {
      starting_value=
        environment.abstract_object_factory(
          member_expr.type(), ns, true, false);
    }
    else
    {
      starting_value=map.at(c);
    }

    copy->map[c]=
      environment.write(starting_value, value, stack, ns, merging_write);
    copy->top=false;
    assert(copy->verify());
    return copy;
  }
  else
  {
    internal_sharing_ptrt<full_struct_abstract_objectt> copy(
      new full_struct_abstract_objectt(*this));

#ifdef DEBUG
    std::cout << "Setting component" << std::endl;
#endif

    irep_idt c=member_expr.get_component_name();

    if(merging_write)
    {
      if(is_top()) // struct is top
      {
        assert(copy->verify());
        return copy;
      }

      assert(!copy->map.empty());

      struct_mapt &m=copy->map;

      struct_mapt::iterator it=m.find(c);

      if(it==m.end()) // component is top
      {
        assert(copy->verify());
        return copy;
      }

      bool dummy;

      it->second=it->second->merge(value, dummy);
    }
    else
    {
      copy->map[c]=value;

      copy->top=false;
      assert(!copy->is_bottom());
    }

    assert(copy->verify());
    return copy;
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
  out << "{";
  for(const auto &entry : map)
  {
    if(entry.first!=map.cbegin()->first)
    {
      out << ", ";
    }
    out << "." << entry.first << "=";
    entry.second->output(out, ai, ns);
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

Function: full_struct_abstract_objectt::merge_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool full_struct_abstract_objectt::merge_state(
  const sharing_ptrt<full_struct_abstract_objectt> op1,
  const sharing_ptrt<full_struct_abstract_objectt> op2)
{
  bool changed;

  // consider top and bottom in parent
  changed=abstract_objectt::merge_state(op1, op2);

  if(is_top() || is_bottom())
  {
    map.clear();
    assert(verify());
    return changed;
  }

  assert(!op1->is_top() && !op2->is_top());
  assert(!op1->is_bottom() && !op2->is_bottom());

  if(op2->is_bottom())
  {
    assert(verify());
    return false;
  }

  if(op1->is_bottom())
  {
    map=op2->map;
    assert(verify());
    return true;
  }


  // at this point both are different from top and bottom
  return abstract_objectt::merge_maps<irep_idt>(op1->map, op2->map, map);

  assert(verify());
}
