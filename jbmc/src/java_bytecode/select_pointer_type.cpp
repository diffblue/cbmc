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
    generic_parameter_recursion_trackingt visited;
    const auto &type = specialize_generics(
      pointer_type, generic_parameter_specialization_map, visited);
    INVARIANT(visited.empty(), "recursion stack must be empty here");
    return type;
  }
  else
  {
    return pointer_type;
  }
}

pointer_typet select_pointer_typet::specialize_generics(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map,
  generic_parameter_recursion_trackingt &visited_nodes) const
{
  if(is_java_generic_parameter(pointer_type))
  {
    const java_generic_parametert &parameter =
      to_java_generic_parameter(pointer_type);
    const irep_idt &parameter_name = parameter.get_name();

    // avoid infinite recursion by looking at each generic argument from
    // previous assignments
    if(visited_nodes.find(parameter_name) != visited_nodes.end())
    {
      const optionalt<pointer_typet> result = get_recursively_instantiated_type(
        parameter_name, generic_parameter_specialization_map);
      return result.has_value() ? result.value() : pointer_type;
    }

    if(generic_parameter_specialization_map.count(parameter_name) == 0)
    {
      // this means that the generic pointer_type has not been specialized
      // in the current context (e.g., the method under test is generic);
      // we return the pointer_type itself which is basically a pointer to
      // its upper bound
      return pointer_type;
    }
    const pointer_typet &type =
      generic_parameter_specialization_map.find(parameter_name)->second.back();

    // generic parameters can be adopted from outer classes or superclasses so
    // we may need to search for the concrete type recursively
    if(!is_java_generic_parameter(type))
      return type;

    visited_nodes.insert(parameter_name);
    const auto returned_type = specialize_generics(
      to_java_generic_parameter(type),
      generic_parameter_specialization_map,
      visited_nodes);
    visited_nodes.erase(parameter_name);
    return returned_type;
  }
  else if(pointer_type.subtype().id() == ID_struct_tag)
  {
    // if the pointer is an array, recursively specialize its element type
    const auto &array_subtype = to_struct_tag_type(pointer_type.subtype());
    if(is_java_array_tag(array_subtype.get_identifier()))
    {
      const typet &array_element_type = java_array_element_type(array_subtype);
      if(array_element_type.id() == ID_pointer)
      {
        const pointer_typet &new_array_type = specialize_generics(
          to_pointer_type(array_element_type),
          generic_parameter_specialization_map,
          visited_nodes);

        pointer_typet replacement_array_type = java_array_type('a');
        replacement_array_type.subtype().set(ID_element_type, new_array_type);
        return replacement_array_type;
      }
    }
  }
  return pointer_type;
}

/// Return the first concrete type instantiation if any such exists. This method
/// is only to be called when \ref select_pointer_typet::specialize_generics
/// cannot find an instantiation due to a loop in its recursion.
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
/// \param parameter_name: The name of the generic parameter type we want to
///   have instantiated
/// \param generic_parameter_specialization_map: Map of type names to
///   specialization stack
/// \return The first instantiated type for the generic type or nothing if no
///   such instantiation exists.
optionalt<pointer_typet>
select_pointer_typet::get_recursively_instantiated_type(
  irep_idt parameter_name,
  generic_parameter_specialization_mapt
    generic_parameter_specialization_map) const
{
  while(true)
  {
    auto types_it = generic_parameter_specialization_map.find(parameter_name);
    INVARIANT(
      types_it != generic_parameter_specialization_map.end(),
      "Type parameter must have a type argument");
    if(types_it->second.empty())
      return {};
    reference_typet type = types_it->second.back();
    types_it->second.pop_back();
    if(!is_java_generic_parameter(type))
      return std::move(type);
    parameter_name = to_java_generic_parameter(type).get_name();
  }
}

std::set<struct_tag_typet>
select_pointer_typet::get_parameter_alternative_types(
  const irep_idt &,
  const irep_idt &,
  const namespacet &) const
{
  return {};
}
