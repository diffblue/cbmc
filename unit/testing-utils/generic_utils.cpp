/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <util/ui_message.h>
#include <java_bytecode/generate_java_generic_type.h>
#include <util/namespace.h>
#include "generic_utils.h"
#include "catch.hpp"
#include "require_type.h"

/// Generic a specalised version of a Java generic class and add it to the
/// symbol table.
/// \param example_type: A reference type that is a specalised generic to use
/// as the base for the specalised version (e.g. a variable of type
/// `Generic<Integer>`
/// \param new_symbol_table: The symbol table to store the new type in
void generic_utils::specialise_generic(
  const java_generic_typet &example_type,
  symbol_tablet &new_symbol_table)
{
  // Should be a fully instantiated generic type
  REQUIRE(
    std::none_of(
      example_type.generic_type_arguments().begin(),
      example_type.generic_type_arguments().end(),
      is_java_generic_parameter));

  namespacet ns(new_symbol_table);
  const typet &class_type = ns.follow(example_type.subtype());
  REQUIRE(
    (is_java_generic_class_type(class_type) ||
     is_java_implicitly_generic_class_type(class_type)));

  // Generate the specialised version.
  ui_message_handlert message_handler;
  generate_java_generic_typet instantiate_generic_type(message_handler);
  instantiate_generic_type(
    to_java_generic_type(example_type), new_symbol_table);
}

/// Helper function to specialise a generic class from a named component of a
/// named class
/// \param class_name: The name of the class that has a generic component.
/// \param component_name: The name of the generic component
/// \param new_symbol_table: The symbol table to use.
void generic_utils::specialise_generic_from_component(
  const irep_idt &class_name,
  const irep_idt &component_name,
  symbol_tablet &new_symbol_table)
{
  const symbolt &harness_symbol = new_symbol_table.lookup_ref(class_name);
  const struct_typet::componentt &harness_component =
    require_type::require_component(
      to_struct_type(harness_symbol.type), component_name);
  generic_utils::specialise_generic(
    to_java_generic_type(harness_component.type()), new_symbol_table);
}
