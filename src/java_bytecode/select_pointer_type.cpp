/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include "select_pointer_type.h"

#include <java_bytecode/get_concrete_class_alphabetically.h>

#include <util/invariant.h>
#include <util/namespace.h>
#include <util/std_types.h>


/// Select what type should be used for a given pointer type. If the class
/// pointed to is abstract then we consider using a subclass of it.
/// \param pointer_type: The pointer type replace
/// \return A pointer type where the subtype may have been modified
pointer_typet select_pointer_typet::operator()(
  const pointer_typet &pointer_type) const
{
  // Currently only replace abstract classes
  // Potentially in the future we might want to consider anything with
  // derived classes
  if(!is_abstract_type(pointer_type))
  {
    return pointer_type;
  }

  // TODO(tkiley): Look to see whether there is a suitable model class to use

  get_concrete_class_alphabeticallyt get_concrete_class_alphabetically(ns);
  const pointer_typet &resolved_type=
    get_concrete_class_alphabetically(pointer_type);

  return resolved_type;
}

/// Find out whether a pointer is pointing to an abstract class or interface
/// \param pointer_type: The type of the pointer
/// \return True if the type pointed to is either an abstract class or an
///   interface.
bool select_pointer_typet::is_abstract_type(
  const pointer_typet &pointer_type) const
{
  const typet &pointing_to_type=ns.follow(pointer_type.subtype());

  // void* pointers should be not considered abstract
  // These happen in Java when initializing the exeception value.
  if(pointing_to_type.id()==ID_empty)
    return false;

  INVARIANT(
    pointing_to_type.id()==ID_struct,
    "All pointers in Java should be to classes");

  const class_typet &class_type=to_class_type(pointing_to_type);
  return class_type.is_class() && class_type.is_abstract();
}
