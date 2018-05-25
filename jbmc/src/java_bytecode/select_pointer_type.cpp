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

/// Select what type should be used for a given pointer type. For the base class
/// we just use the supplied type. Derived classes can override this behaviour
/// to provide more sophisticated type selection. Generic parameters are
/// replaced with their concrete type.
/// \param pointer_type: The pointer type replace
/// \param generic_parameter_specialization_map map of types for all generic
/// parameters in the current scope
/// \return A pointer type where the subtype may have been modified
pointer_typet select_pointer_typet::convert_pointer_type(
  const pointer_typet &pointer_type,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map,
  const namespacet &ns) const
{
  // if we have a map of generic parameters -> types and the pointer is
  // a generic parameter, specialize it with concrete types
  if(!generic_parameter_specialization_map.empty())
  {
    generic_parameter_recursion_trackingt visited;
    auto type = specialize_generics(
      pointer_type, generic_parameter_specialization_map, visited);
    INVARIANT(visited.empty(), "recursion stack must be empty here");
    return type;
  }
  else
  {
    return pointer_type;
  }
}

/// Specialize generic parameters in a pointer type based on the current map
/// of parameters -> types. We specialize generics if the pointer is a java
/// generic parameter or an array with generic parameters (java generic types
/// are specialized recursively, their concrete types are already stored in
/// the map and will be retrieved when needed e.g., to initialize fields).
/// Example:
/// - generic type: T
/// - map: T -> U; U -> String
/// - result: String
///
/// - generic type: T[]
/// - map: T -> U; U -> String
/// - result: String
/// \param pointer_type pointer to be specialized
/// \param generic_parameter_specialization_map map of types for all generic
/// parameters in the current scope
/// \return pointer type where generic parameters are replaced with concrete
/// types, if set in the current scope
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

    // if we have already seen this before, we will not learn any additional
    // information from further recursion, only cause a segmentation fault.
    if(visited_nodes.find(parameter_name) != visited_nodes.end())
    {
      optionalt<pointer_typet> result = get_instantiated_type(
        parameter_name, generic_parameter_specialization_map);
      if(result.has_value())
      {
        return result.value();
      }
      throw "no infinite recursion";
    }

    // generic parameters can be adopted from outer classes or superclasses so
    // we may need to search for the concrete type recursively
    if(is_java_generic_parameter(type))
    {
      visited_nodes.insert(parameter_name);
      auto returned_type = specialize_generics(
        to_java_generic_parameter(type),
        generic_parameter_specialization_map,
        visited_nodes);
      visited_nodes.erase(parameter_name);
      return returned_type;
    }
    else
    {
      return type;
    }
  }
  else if(pointer_type.subtype().id() == ID_symbol)
  {
    // if the pointer is an array, recursively specialize its element type
    const symbol_typet &array_subtype = to_symbol_type(pointer_type.subtype());
    if(is_java_array_tag(array_subtype.get_identifier()))
    {
      const typet &array_element_type = java_array_element_type(array_subtype);
      if(array_element_type.id() == ID_pointer)
      {
        const pointer_typet &new_array_type = specialize_generics(
          to_pointer_type(array_element_type),
          generic_parameter_specialization_map, visited_nodes);

        pointer_typet replacement_array_type = java_array_type('a');
        replacement_array_type.subtype().set(ID_C_element_type, new_array_type);
        return replacement_array_type;
      }
    }
  }
  return pointer_type;
}

/// Return the first concrete type instantiation if any such exists.
/// \param parameter_name The name of the generic parameter type we want to have
///   instantiated
/// \param generic_specialization_map Map of type names to specialization stack
/// \param depth start depth for instantiation search
/// \return the first instantiated type for the generic type or nothing if no
/// such instantiation exists.
optionalt<pointer_typet> select_pointer_typet::get_instantiated_type(
  const irep_idt &parameter_name,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map) const
{
  generic_parameter_recursion_trackingt visited;
  const auto retval = get_instantiated_type(
    parameter_name, generic_parameter_specialization_map, visited, 0);
  INVARIANT(visited.empty(), "recursion set must be empty here");
  return retval;
}

/// See above, the additional parameter just tracks the recursion to prevent
/// visiting the same depth again.
/// \param visited tracks the visited parameter names
optionalt<pointer_typet> select_pointer_typet::get_instantiated_type(
  const irep_idt &parameter_name,
  const generic_parameter_specialization_mapt
    &generic_parameter_specialization_map,
  generic_parameter_recursion_trackingt &visited,
  const size_t depth) const
{
  // Get the pointed to instantiation type at the desired stack depth.
  // - f this type is not a generic type, it is returned as a valid
  //   instantiation
  // - if another recursion at this depth level is found, the search depth is
  //   increased
  // - if nothing can be found an empty optional is returned

  if(
    generic_parameter_specialization_map.find(parameter_name) !=
    generic_parameter_specialization_map.end())
  {
    const auto &replacements =
      generic_parameter_specialization_map.find(parameter_name)->second;

    // max depth reached and nothing found
    if(replacements.size() <= depth)
      return {};

    // Check if there is a recursion loop, if yes increase search depth
    if(visited.find(parameter_name) != visited.end())
    {
      visited.clear();
      return get_instantiated_type(
        parameter_name, generic_parameter_specialization_map, visited, depth+1);
    }
    else
    {
      const size_t index = (replacements.size() - depth) - 1;
      const auto &type = replacements[index];
      {
        if(!is_java_generic_parameter(type))
        {
          return type;
        }
        else
        {
          visited.insert(parameter_name);
          const auto &gen_type = to_java_generic_parameter(type).type_variable();
          const auto val = get_instantiated_type(
            gen_type.get_identifier(),
            generic_parameter_specialization_map,
            visited,
            depth);
          visited.erase(parameter_name);
          return val;
        }
      }
    }
  }
  // parameter_name not found in map
  else
  {
    UNREACHABLE;
  }
}
