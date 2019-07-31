/// Author: Diffblue Ltd.

#ifndef CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_KEYS_H
#define CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_KEYS_H

#include "select_pointer_type.h"
#include "java_types.h"

/// \file
/// Generic-parameter-specialization-map entries owner class.
/// Generic-parameter-specialization-map maps generic parameters to a stack
/// of their types in (every depth of) the current scope. This class adds
/// entries to the map for a particular scope, and ensures that they are erased
/// on leaving that scope.
class generic_parameter_specialization_map_keyst
{
private:
  /// Generic parameter specialization map to modify
  generic_parameter_specialization_mapt &generic_parameter_specialization_map;
  /// Key of the container to pop on destruction
  optionalt<std::size_t> container_id;

public:
  /// Initialize a generic-parameter-specialization-map entry owner operating
  /// on a given map. Initially it does not own any map entry.
  /// \param generic_parameter_specialization_map: map to operate on.
  explicit generic_parameter_specialization_map_keyst(
    generic_parameter_specialization_mapt &generic_parameter_specialization_map)
    : generic_parameter_specialization_map(generic_parameter_specialization_map)
  {
  }

  /// Removes the top of the stack for each key in erase_keys from the
  /// controlled map.
  ~generic_parameter_specialization_map_keyst()
  {
    if(container_id)
      generic_parameter_specialization_map.pop(*container_id);
  }

  // Objects of these class cannot be copied in any way - delete the copy
  // constructor and copy assignment operator
  generic_parameter_specialization_map_keyst(
    const generic_parameter_specialization_map_keyst &) = delete;
  generic_parameter_specialization_map_keyst &
  operator=(const generic_parameter_specialization_map_keyst &) = delete;

  void insert(
    const pointer_typet &pointer_type,
    const typet &pointer_subtype_struct);

  void insert(const struct_tag_typet &, const typet &symbol_struct);
};

#endif // CPROVER_JAVA_BYTECODE_GENERIC_PARAMETER_SPECIALIZATION_MAP_KEYS_H
