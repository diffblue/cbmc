/// Author: Diffblue Ltd.

#include "generic_parameter_specialization_map_keys.h"

#include <iterator>

/// \param type Source type
/// \return The vector of implicitly generic and (explicitly) generic type
/// parameters of the given type.
const std::vector<java_generic_parametert>
get_all_generic_parameters(const typet &type)
{
  PRECONDITION(
    is_java_generic_class_type(type) ||
    is_java_implicitly_generic_class_type(type));
  std::vector<java_generic_parametert> generic_parameters;
  if(is_java_implicitly_generic_class_type(type))
  {
    const java_implicitly_generic_class_typet &implicitly_generic_class =
      to_java_implicitly_generic_class_type(to_java_class_type(type));
    generic_parameters.insert(
      generic_parameters.end(),
      implicitly_generic_class.implicit_generic_types().begin(),
      implicitly_generic_class.implicit_generic_types().end());
  }
  if(is_java_generic_class_type(type))
  {
    const java_generic_class_typet &generic_class =
      to_java_generic_class_type(to_java_class_type(type));
    generic_parameters.insert(
      generic_parameters.end(),
      generic_class.generic_types().begin(),
      generic_class.generic_types().end());
  }
  return generic_parameters;
}

/// Add pairs to the controlled map. Own the keys and pop from their stack
/// on destruction; otherwise do nothing.
/// \param parameters generic parameters that are the keys of the pairs to add
/// \param types a type to add for each parameter
void generic_parameter_specialization_map_keyst::insert_pairs(
  const std::vector<java_generic_parametert> &parameters,
  const std::vector<reference_typet> &types)
{
  INVARIANT(erase_keys.empty(), "insert_pairs should only be called once");
  PRECONDITION(parameters.size() == types.size());

  // Pair up the parameters and types for easier manipulation later
  std::vector<std::pair<java_generic_parametert, reference_typet>> pairs;
  pairs.reserve(parameters.size());
  std::transform(
    parameters.begin(),
    parameters.end(),
    types.begin(),
    std::back_inserter(pairs),
    [&](java_generic_parametert param, reference_typet type)
    {
      return std::make_pair(param, type);
    });

  for(const auto &pair : pairs)
  {
    // Only add the pair if the type is not the parameter itself, e.g.,
    // pair.first = pair.second = java::A::T. This can happen for example
    // when initiating a pointer to an implicitly java generic class type
    // in gen_nondet_init and would result in a loop when the map is used
    // to look up the type of the parameter.
    if(
      !(is_java_generic_parameter(pair.second) &&
        to_java_generic_parameter(pair.second).get_name() ==
          pair.first.get_name()))
    {
      const irep_idt &key = pair.first.get_name();
      if(generic_parameter_specialization_map.count(key) == 0)
        generic_parameter_specialization_map.emplace(
          key, std::vector<reference_typet>());
      (*generic_parameter_specialization_map.find(key))
        .second.push_back(pair.second);

      // We added something, so pop it when this is destroyed:
      erase_keys.push_back(key);
    }
  }
}

/// Add a pair of a parameter and its types for each generic parameter of the
/// given generic pointer type to the controlled map. Own the keys and pop
/// from their stack on destruction; otherwise do nothing.
/// \param pointer_type pointer type to get the specialized generic types from
/// \param pointer_subtype_struct struct type to which the generic pointer
/// points, must be generic if the pointer is generic
void generic_parameter_specialization_map_keyst::insert_pairs_for_pointer(
  const pointer_typet &pointer_type,
  const typet &pointer_subtype_struct)
{
  if(is_java_generic_type(pointer_type))
  {
    // The supplied type must be the full type of the pointer's subtype
    PRECONDITION(
      pointer_type.subtype().get(ID_identifier) ==
      pointer_subtype_struct.get(ID_name));

    // If the pointer points to:
    // - an incomplete class or
    // - a class that is neither generic nor implicitly generic (this
    //  may be due to unsupported class signature)
    // then ignore the generic types in the pointer and do not add any pairs.
    // TODO TG-1996 should decide how mocking and generics should work
    // together. Currently an incomplete class is never marked as generic. If
    // this changes in TG-1996 then the condition below should be updated.
    if(
      !to_java_class_type(pointer_subtype_struct).get_is_stub() &&
      (is_java_generic_class_type(pointer_subtype_struct) ||
       is_java_implicitly_generic_class_type(pointer_subtype_struct)))
    {
      const java_generic_typet &generic_pointer =
        to_java_generic_type(pointer_type);
      const std::vector<java_generic_parametert> &generic_parameters =
        get_all_generic_parameters(pointer_subtype_struct);

      INVARIANT(
        generic_pointer.generic_type_arguments().size() ==
          generic_parameters.size(),
        "All generic parameters of the pointer type need to be specified");

      insert_pairs(
        generic_parameters, generic_pointer.generic_type_arguments());
    }
  }
}

/// Add a pair of a parameter and its types for each generic parameter of the
/// given generic symbol type to the controlled map. This function is used
/// for generic bases (superclass or interfaces) where the reference to it is
/// in the form of a symbol rather than a pointer (as opposed to the function
/// insert_pairs_for_pointer). Own the keys and pop from their stack
/// on destruction; otherwise do nothing.
/// \param struct_tag_type symbol type to get the specialized generic types from
/// \param symbol_struct struct type of the symbol type, must be generic if
/// the symbol is generic
void generic_parameter_specialization_map_keyst::insert_pairs_for_symbol(
  const struct_tag_typet &struct_tag_type,
  const typet &symbol_struct)
{
  // If the struct is:
  // - an incomplete class or
  // - a class that is neither generic nor implicitly generic (this
  //  may be due to unsupported class signature)
  // then ignore the generic types in the struct_tag_type and do not add any
  // pairs.
  // TODO TG-1996 should decide how mocking and generics should work
  // together. Currently an incomplete class is never marked as generic. If
  // this changes in TG-1996 then the condition below should be updated.
  if(
    is_java_generic_struct_tag_type(struct_tag_type) &&
    !to_java_class_type(symbol_struct).get_is_stub() &&
    (is_java_generic_class_type(symbol_struct) ||
     is_java_implicitly_generic_class_type(symbol_struct)))
  {
    const java_generic_struct_tag_typet &generic_symbol =
      to_java_generic_struct_tag_type(struct_tag_type);

    const std::vector<java_generic_parametert> &generic_parameters =
      get_all_generic_parameters(symbol_struct);

    INVARIANT(
      generic_symbol.generic_types().size() == generic_parameters.size(),
      "All generic parameters of the superclass need to be concretized");

    insert_pairs(generic_parameters, generic_symbol.generic_types());
  }
}
