/*******************************************************************\

Module: Extract class identifier

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Extract class identifier

#include "class_identifier.h"

#include <util/std_expr.h>
#include <util/c_types.h>
#include <util/namespace.h>

/// \par parameters: Struct expression
/// \return Member expression giving the clsid field of the input, or its
///   parent, grandparent, etc.
static exprt build_class_identifier(
  const exprt &src,
  const namespacet &ns)
{
  // the class identifier is in the root class
  exprt e=src;

  while(1)
  {
    const typet &type=ns.follow(e.type());
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    assert(!components.empty());

    const auto &first_member_name=components.front().get_name();
    member_exprt member_expr(
      e,
      first_member_name,
      components.front().type());

    if(first_member_name=="@class_identifier")
    {
      // found it
      return member_expr;
    }
    else
    {
      e.swap(member_expr);
    }
  }
}

/// \par parameters: Pointer expression of any pointer type, including void*,
/// and a recommended access type if the pointer is void-typed.
/// \return Member expression to access a class identifier, as above.
exprt get_class_identifier_field(
  const exprt &this_expr_in,
  const symbol_typet &suggested_type,
  const namespacet &ns)
{
  // Get a pointer from which we can extract a clsid.
  // If it's already a pointer to an object of some sort, just use it;
  // if it's void* then use the suggested type.

  exprt this_expr=this_expr_in;
  assert(this_expr.type().id()==ID_pointer &&
         "Non-pointer this-arg in remove-virtuals?");
  const auto &points_to=this_expr.type().subtype();
  if(points_to==empty_typet())
    this_expr=typecast_exprt(this_expr, pointer_type(suggested_type));
  exprt deref=dereference_exprt(this_expr, this_expr.type().subtype());
  return build_class_identifier(deref, ns);
}
