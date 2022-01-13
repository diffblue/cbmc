/// Author: Diffblue Ltd.

#include "generic_parameter_specialization_map_keys.h"

/// Add the parameters and their types for each generic parameter of the
/// given generic pointer type to the map.
/// Own the keys and pop from their stack on destruction.
/// \param pointer_type: pointer type to get the specialized generic types from
/// \param pointer_subtype_struct: struct type to which the generic pointer
///   points, must be generic if the pointer is generic
void generic_parameter_specialization_map_keyst::insert(
  const pointer_typet &pointer_type,
  const typet &pointer_subtype_struct)
{
  // Use a fresh generic_parameter_specialization_map_keyst for each scope
  PRECONDITION(!container_id);
  if(!is_java_generic_type(pointer_type))
    return;
  // The supplied type must be the full type of the pointer's subtype
  PRECONDITION(
    pointer_type.base_type().get(ID_identifier) ==
    pointer_subtype_struct.get(ID_name));

  // If the pointer points to:
  // - an incomplete class or
  // - a class that is neither generic nor implicitly generic (this
  //   may be due to unsupported class signature)
  // then ignore the generic types in the pointer and do not add an entry.
  // TODO TG-1996 should decide how mocking and generics should work
  //   together. Currently an incomplete class is never marked as generic. If
  //   this changes in TG-1996 then the condition below should be updated.
  if(to_java_class_type(pointer_subtype_struct).get_is_stub())
    return;
  if(
    !is_java_generic_class_type(pointer_subtype_struct) &&
    !is_java_implicitly_generic_class_type(pointer_subtype_struct))
  {
    return;
  }

  const java_generic_typet &generic_pointer =
    to_java_generic_type(pointer_type);

  const std::vector<java_generic_parametert> &generic_parameters =
    get_all_generic_parameters(pointer_subtype_struct);
  const java_generic_typet::generic_type_argumentst &type_args =
    generic_pointer.generic_type_arguments();
  INVARIANT(
    type_args.size() == generic_parameters.size(),
    "All generic parameters of the pointer type need to be specified");

  container_id =
    generic_parameter_specialization_map.insert(generic_parameters, type_args);
}

/// Add the parameters and their types for each generic parameter of the
/// given generic symbol type to the map.
/// This function is used for generic bases (superclass or interfaces) where
/// the reference to it is in the form of a symbol rather than a pointer.
/// Own the keys and pop from their stack on destruction.
/// \param struct_tag_type: symbol type to get the specialized generic types
///   from
/// \param symbol_struct: struct type of the symbol type, must be generic if
///   the symbol is generic
void generic_parameter_specialization_map_keyst::insert(
  const struct_tag_typet &struct_tag_type,
  const typet &symbol_struct)
{
  // Use a fresh generic_parameter_specialization_map_keyst for each scope
  PRECONDITION(!container_id);
  if(!is_java_generic_struct_tag_type(struct_tag_type))
    return;
  // The supplied type must be the full type of the pointer's subtype
  PRECONDITION(
    struct_tag_type.get(ID_identifier) == symbol_struct.get(ID_name));

  // If the struct is:
  // - an incomplete class or
  // - a class that is neither generic nor implicitly generic (this
  //  may be due to unsupported class signature)
  // then ignore the generic types in the struct and do not add an entry.
  // TODO TG-1996 should decide how mocking and generics should work
  //   together. Currently an incomplete class is never marked as generic. If
  //   this changes in TG-1996 then the condition below should be updated.
  if(to_java_class_type(symbol_struct).get_is_stub())
    return;
  if(
    !is_java_generic_class_type(symbol_struct) &&
    !is_java_implicitly_generic_class_type(symbol_struct))
  {
    return;
  }

  const java_generic_struct_tag_typet &generic_symbol =
    to_java_generic_struct_tag_type(struct_tag_type);

  const std::vector<java_generic_parametert> &generic_parameters =
    get_all_generic_parameters(symbol_struct);
  const java_generic_typet::generic_type_argumentst &type_args =
    generic_symbol.generic_types();
  INVARIANT(
    type_args.size() == generic_parameters.size(),
    "All generic parameters of the superclass need to be concretized");

  container_id =
    generic_parameter_specialization_map.insert(generic_parameters, type_args);
}
