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
  if(type.id() == ID_struct || type.id() == ID_union)
  {
    // Not allowed in PODs:
    // * Non-PODs
    // * Constructors/Destructors (including template constructors)
    // * virtuals
    // * private/protected, unless static
    // * overloading assignment operator
    //
    // [class.union]/2: a union may have user-declared special member
    // functions (constructors, destructor) and other member functions, in
    // which case it is not a POD/trivial type and must be initialised via a
    // constructor rather than by conversion.  The same component checks apply
    // as for a struct; a union has no base classes.

    if(type.get_bool("has_template_constructor"))
      return false;
    // * Base classes

    const struct_union_typet &struct_type = to_struct_union_type(type);

    if(type.id() == ID_struct && !to_struct_type(type).bases().empty())
      return false;

    const struct_union_typet::componentst &components =
      struct_type.components();

    for(const auto &c : components)
    {
      if(c.get_bool(ID_is_type))
        continue;

      // Padding inserted for ABI layout ([class.bit]/[basic.align]) is not a
      // member ([class.mem]): it has no access specifier and must not affect
      // the triviality/POD-ness of the class.
      if(c.get_is_padding())
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

      // Only check non-static data members for POD-ness
      if(
        sub_type.id() != ID_code && !c.get_bool(ID_is_static) &&
        !cpp_is_pod(sub_type))
      {
        return false;
      }
    }

    return true;
  }
  else if(type.id()==ID_array)
  {
    return cpp_is_pod(to_array_type(type).element_type());
  }
  else if(type.id() == ID_vector)
  {
    return cpp_is_pod(to_vector_type(type).element_type());
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
