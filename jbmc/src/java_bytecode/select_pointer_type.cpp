/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include "select_pointer_type.h"

#include "generic_parameter_specialization_map.h"
#include "java_types.h"

#include <util/std_types.h>

pointer_typet select_pointer_typet::convert_pointer_type(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map,
  const namespacet &) const
{
  return specialize_generics(
    pointer_type, generic_parameter_specialization_map);
}

pointer_typet select_pointer_typet::specialize_generics(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map) const
{
  auto parameter = type_try_dynamic_cast<java_generic_parametert>(pointer_type);
  if(parameter != nullptr)
  {
    irep_idt parameter_name = parameter->get_name();

    // Make a local copy of the specialization map to unwind
    generic_parameter_specialization_mapt spec_map_copy =
      generic_parameter_specialization_map;
    while(true)
    {
      const optionalt<reference_typet> specialization =
        spec_map_copy.pop(parameter_name);
      if(!specialization)
      {
        // This means that the generic pointer_type has not been specialized
        // in the current context (e.g., the method under test is generic);
        // we return the pointer_type itself which is a pointer to its upper
        // bound
        return pointer_type;
      }

      if(!is_java_generic_parameter(*specialization))
        return *specialization;
      parameter_name = to_java_generic_parameter(*specialization).get_name();
    }
  }

  auto base_type =
    type_try_dynamic_cast<struct_tag_typet>(pointer_type.base_type());
  if(base_type != nullptr && is_java_array_tag(base_type->get_identifier()))
  {
    // if the pointer is an array, recursively specialize its element type
    const auto *array_element_type =
      type_try_dynamic_cast<pointer_typet>(java_array_element_type(*base_type));
    if(array_element_type == nullptr)
      return pointer_type;

    const pointer_typet &new_array_type = specialize_generics(
      *array_element_type, generic_parameter_specialization_map);

    pointer_typet replacement_array_type = java_array_type('a');
    replacement_array_type.base_type().set(ID_element_type, new_array_type);
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
