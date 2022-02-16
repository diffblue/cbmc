/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/pointer_expr.h>

bool cpp_typecheckt::cpp_is_pod(const typet &type) const
{
  if(type.id()==ID_struct)
  {
    // Not allowed in PODs:
    // * Non-PODs
    // * Constructors/Destructors
    // * virtuals
    // * private/protected, unless static
    // * overloading assignment operator
    // * Base classes

    const struct_typet &struct_type=to_struct_type(type);

    if(!struct_type.bases().empty())
      return false;

    const struct_typet::componentst &components=
      struct_type.components();

    for(const auto &c : components)
    {
      if(c.get_bool(ID_is_type))
        continue;

      if(c.get_base_name() == "operator=")
        return false;

      if(c.get_bool(ID_is_virtual))
        return false;

      const typet &sub_type = c.type();

      if(sub_type.id()==ID_code)
      {
        if(c.get_bool(ID_is_virtual))
          return false;

        const typet &comp_return_type = to_code_type(sub_type).return_type();

        if(
          comp_return_type.id() == ID_constructor ||
          comp_return_type.id() == ID_destructor)
        {
          return false;
        }
      }
      else if(c.get(ID_access) != ID_public && !c.get_bool(ID_is_static))
        return false;

      if(!cpp_is_pod(sub_type))
        return false;
    }

    return true;
  }
  else if(type.id()==ID_array)
  {
    return cpp_is_pod(to_array_type(type).element_type());
  }
  else if(type.id()==ID_pointer)
  {
    if(is_reference(type)) // references are not PODs
      return false;

    // but pointers are PODs!
    return true;
  }
  else if(type.id() == ID_struct_tag ||
          type.id() == ID_union_tag)
  {
    const symbolt &symb = lookup(to_tag_type(type));
    DATA_INVARIANT(symb.is_type, "tag symbol is a type");
    return cpp_is_pod(symb.type);
  }

  // everything else is POD
  return true;
}
