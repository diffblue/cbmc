/*******************************************************************\

Module: JAVA Pointer Casts

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Pointer Casts

#include "java_pointer_casts.h"

#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include "java_types.h"

/// dereference pointer expression
/// \return dereferenced pointer
static exprt clean_deref(const exprt &ptr)
{
  return ptr.id() == ID_address_of ? to_address_of_expr(ptr).object()
                                   : dereference_exprt{ptr};
}

/// \par parameters: pointer
/// target type to search
/// \return true iff a super class with target type is found
bool find_superclass_with_type(
  exprt &ptr,
  const typet &target_type,
  const namespacet &ns)
{
  PRECONDITION(ptr.type().id() == ID_pointer);
  while(true)
  {
    const typet ptr_base = ns.follow(to_pointer_type(ptr.type()).base_type());

    if(ptr_base.id()!=ID_struct)
      return false;

    const struct_typet &base_struct=to_struct_type(ptr_base);

    if(base_struct.components().empty())
      return false;

    const typet &first_field_type=base_struct.components()[0].type();
    ptr=clean_deref(ptr);
    // Careful not to use the followed type here, as stub types may be
    // extended by later method conversion adding fields (e.g. an access
    // against x->y might add a new field `y` to the type of `*x`)
    ptr=member_exprt(
      ptr,
      base_struct.components()[0].get_name(),
      first_field_type);
    ptr=address_of_exprt(ptr);

    // Compare the real (underlying) type, as target_type is already a non-
    // symbolic type.
    if(ns.follow(first_field_type)==target_type)
      return true;
  }
}

/// \par parameters: raw pointer
/// target type
/// namespace
/// \return cleaned up typecast expression
exprt make_clean_pointer_cast(
  const exprt &rawptr,
  const pointer_typet &target_type,
  const namespacet &ns)
{
  const exprt &ptr = skip_typecast(rawptr);

  PRECONDITION(ptr.type().id()==ID_pointer);

  if(ptr.type()==target_type)
    return ptr;

  if(
    to_pointer_type(ptr.type()).base_type() == java_void_type() ||
    target_type.base_type() == java_void_type())
  {
    return typecast_exprt(ptr, target_type);
  }

  const typet &target_base = ns.follow(target_type.base_type());

  exprt bare_ptr=ptr;
  while(bare_ptr.id()==ID_typecast)
  {
    INVARIANT(
      bare_ptr.type().id() == ID_pointer,
      "Non-pointer in make_clean_pointer_cast?");
    if(to_pointer_type(bare_ptr.type()).base_type() == java_void_type())
      bare_ptr = to_typecast_expr(bare_ptr).op();
  }

  INVARIANT(
    bare_ptr.type().id() == ID_pointer,
    "Non-pointer in make_clean_pointer_cast?");

  if(bare_ptr.type()==target_type)
    return bare_ptr;

  exprt superclass_ptr=bare_ptr;
  // Looking at base types discards generic qualifiers (because those are
  // recorded on the pointer, not the pointee), so it may still be necessary
  // to use a cast to reintroduce the qualifier (for example, the base might
  // be recorded as a List, when we're looking for a List<E>)
  if(find_superclass_with_type(superclass_ptr, target_base, ns))
    return typecast_exprt::conditional_cast(superclass_ptr, target_type);

  return typecast_exprt(bare_ptr, target_type);
}
