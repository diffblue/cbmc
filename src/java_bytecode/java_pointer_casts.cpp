/*******************************************************************\

Module: JAVA Pointer Casts

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Pointer Casts

#include "java_pointer_casts.h"

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/namespace.h>

/// dereference pointer expression
/// \return dereferenced pointer
static exprt clean_deref(const exprt &ptr)
{
  return ptr.id()==ID_address_of
             ? ptr.op0()
             : dereference_exprt(ptr, ptr.type().subtype());
}

/// \par parameters: pointer
/// target type to search
/// \return true iff a super class with target type is found
bool find_superclass_with_type(
  exprt &ptr,
  const typet &target_type,
  const namespacet &ns)
{
  assert(ptr.type().id()==ID_pointer);
  while(true)
  {
    const typet ptr_base=ns.follow(ptr.type().subtype());

    if(ptr_base.id()!=ID_struct)
      return false;

    const struct_typet &base_struct=to_struct_type(ptr_base);

    if(base_struct.components().empty())
      return false;

    const typet &first_field_type=
        ns.follow(base_struct.components()[0].type());
    ptr=clean_deref(ptr);
    ptr=member_exprt(
      ptr,
      base_struct.components()[0].get_name(),
      first_field_type);
    ptr=address_of_exprt(ptr);

    if(first_field_type==target_type)
      return true;
  }
}


/// \par parameters: input expression
/// \return recursively search target of typecast
static const exprt &look_through_casts(const exprt &in)
{
  if(in.id()==ID_typecast)
  {
    assert(in.type().id()==ID_pointer);
    return look_through_casts(in.op0());
  }
  else
    return in;
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
  const exprt &ptr=look_through_casts(rawptr);

  PRECONDITION(ptr.type().id()==ID_pointer);

  if(ptr.type()==target_type)
    return ptr;

  if(ptr.type().subtype()==empty_typet() ||
     target_type.subtype()==empty_typet())
    return typecast_exprt(ptr, target_type);

  const typet &target_base=ns.follow(target_type.subtype());

  exprt bare_ptr=ptr;
  while(bare_ptr.id()==ID_typecast)
  {
    assert(
      bare_ptr.type().id()==ID_pointer &&
      "Non-pointer in make_clean_pointer_cast?");
    if(bare_ptr.type().subtype()==empty_typet())
      bare_ptr=bare_ptr.op0();
  }

  assert(
    bare_ptr.type().id()==ID_pointer &&
    "Non-pointer in make_clean_pointer_cast?");

  if(bare_ptr.type()==target_type)
    return bare_ptr;

  exprt superclass_ptr=bare_ptr;
  if(find_superclass_with_type(superclass_ptr, target_base, ns))
    return superclass_ptr;

  return typecast_exprt(bare_ptr, target_type);
}
