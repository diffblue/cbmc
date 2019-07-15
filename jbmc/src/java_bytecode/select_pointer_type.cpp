/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include "select_pointer_type.h"
#include "java_types.h"
#include <util/std_types.h>

pointer_typet select_pointer_typet::convert_pointer_type(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map,
  const namespacet &ns) const
{
  (void)ns; // unused parameter
  // if we have a map of generic parameters -> types and the pointer is
  // a generic parameter, specialize it with concrete types
  if(!generic_parameter_specialization_map.empty())
  {
    return specialize_generics(
      pointer_type, generic_parameter_specialization_map);
  }
  else
  {
    return pointer_type;
  }
}

/// Return the first concrete type instantiation if any such exists.
///
/// Example:
/// `class MyGeneric<T,U> { MyGeneric<U,T> gen; T t;}`
/// When instantiating `MyGeneric<Integer,String> my` we need to for example
/// resolve the type of `my.gen.t`. The map would in this context contain
/// - T -> (Integer, U)
/// - U -> (String, T)
///
/// Note that the top of the stacks for T and U create a recursion T -> U,
/// U-> T. We want to break it and specialize `T my.gen.t` to `String my.gen.t`.
/// \param pointer_type: The pointer type to specialize
/// \param generic_parameter_specialization_map: Map of type names to
///   specialization stack
/// \return The first instantiated type for the generic type or nothing if no
///   such instantiation exists.
pointer_typet select_pointer_typet::specialize_generics(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map) const
{
  auto parameter = type_try_dynamic_cast<java_generic_parametert>(pointer_type);
  if(parameter != nullptr)
  {
    irep_idt parameter_name = parameter->get_name();

    generic_parameter_specialization_mapt spec_map_copy =
      generic_parameter_specialization_map;
    while(true)
    {
      auto types_it = spec_map_copy.find(parameter_name);
      if(types_it == spec_map_copy.end() || types_it->second.empty())
      {
        // This means that the generic pointer_type has not been specialized
        // in the current context (e.g., the method under test is generic);
        // we return the pointer_type itself which is a pointer to its upper
        // bound
        return pointer_type;
      }
      const reference_typet &type = types_it->second.back();
      types_it->second.pop_back();
      if(!is_java_generic_parameter(type))
        return type;
      parameter_name = to_java_generic_parameter(type).get_name();
    }
  }

  auto subtype =
    type_try_dynamic_cast<struct_tag_typet>(pointer_type.subtype());
  if(subtype != nullptr && is_java_array_tag(subtype->get_identifier()))
  {
    // if the pointer is an array, recursively specialize its element type
    auto array_element_type =
      type_try_dynamic_cast<pointer_typet>(java_array_element_type(*subtype));
    if(array_element_type == nullptr)
      return pointer_type;

    const pointer_typet &new_array_type = specialize_generics(
      *array_element_type,
      generic_parameter_specialization_map);

    pointer_typet replacement_array_type = java_array_type('a');
    replacement_array_type.subtype().set(ID_element_type, new_array_type);
    return replacement_array_type;
  }

  return pointer_type;
}

std::set<struct_tag_typet>
select_pointer_typet::get_parameter_alternative_types(
  const irep_idt &,
  const irep_idt &,
  const namespacet &) const
{
  return {};
}
