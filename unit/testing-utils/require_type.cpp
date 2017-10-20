/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include "require_type.h"

#include <testing-utils/catch.hpp>
#include <util/base_type.h>

/// Checks a type is a pointer type optionally with a specific subtype
/// \param type: The type to check
/// \param subtype: An optional subtype. If provided, checks the subtype of the
///   pointer is this.
/// \return A cast to pointer_typet version of type
pointer_typet require_type::require_pointer(
  const typet &type,
  const optionalt<typet> &subtype)
{
  REQUIRE(type.id() == ID_pointer);
  const pointer_typet &pointer = to_pointer_type(type);

  if(subtype)
  {
    // TODO: use base_type_eq
    REQUIRE(pointer.subtype() == subtype.value());
  }
  return pointer;
}

/// Checks a struct like type has a component with a specific name
/// \param struct_type: The structure that should have the component
/// \param component_name: The name of the component
/// \return The component with the specified name
struct_union_typet::componentt require_type::require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name)
{
  const auto &componet = std::find_if(
    struct_type.components().begin(),
    struct_type.components().end(),
    [&component_name](const struct_union_typet::componentt &component) {
      return component.get_name() == component_name;
    });

  REQUIRE(componet != struct_type.components().end());
  return *componet;
}
