/*******************************************************************\

Module: Extract class identifier

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "class_identifier.h"

#include <util/std_expr.h>

/*******************************************************************\

Function: build_class_identifier

  Inputs: Struct expression

 Outputs: Member expression giving the clsid field of the input,
          or its parent, grandparent, etc.

 Purpose:

\*******************************************************************/

static exprt build_class_identifier(
  const exprt &src,
  const namespacet &ns)
{
  // the class identifier is in the root class
  exprt e=src;

  while(1)
  {
    const typet &type=ns.follow(e.type());
    assert(type.id()==ID_struct);

    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    assert(!components.empty());

    member_exprt member_expr(
      e,
      components.front().get_name(),
      components.front().type());

    if(components.front().get_name()=="@class_identifier")
    {
      // found it
      return member_expr;
    }
    else
    {
      e=member_expr;
    }
  }
}

/*******************************************************************\

Function: get_class_identifier_field

  Inputs: Pointer expression of any pointer type, including void*,
          and a recommended access type if the pointer is void-typed.

 Outputs: Member expression to access a class identifier, as above.

 Purpose:

\*******************************************************************/

exprt get_class_identifier_field(
  exprt this_expr,
  const symbol_typet &suggested_type,
  const namespacet &ns)
{
  // Get a pointer from which we can extract a clsid.
  // If it's already a pointer to an object of some sort, just use it;
  // if it's void* then use the suggested type.

  assert(this_expr.type().id()==ID_pointer &&
         "Non-pointer this-arg in remove-virtuals?");
  const auto& points_to=this_expr.type().subtype();
  if(points_to==empty_typet())
    this_expr=typecast_exprt(this_expr, pointer_typet(suggested_type));
  exprt deref=dereference_exprt(this_expr, this_expr.type().subtype());
  return build_class_identifier(deref, ns);
}
