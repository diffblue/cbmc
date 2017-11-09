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
    std::all_of(
      example_type.generic_type_variables().begin(),
      example_type.generic_type_variables().end(),
      is_java_generic_inst_parameter));

  namespacet ns(new_symbol_table);
  const typet &class_type = ns.follow(example_type.subtype());
  REQUIRE(is_java_generic_class_type(class_type));

  // Generate the specialised version.
  ui_message_handlert message_handler;
  generate_java_generic_typet instantiate_generic_type(message_handler);
  instantiate_generic_type(
    to_java_generic_type(example_type), new_symbol_table);
}
