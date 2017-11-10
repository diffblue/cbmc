/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>

SCENARIO(
  "parse_derived_generic_class_inst",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "DerivedGenericInst", "./java_bytecode/java_bytecode_parse_generics");

  THEN("There should be a symbol for the DerivedGenericInst class")
  {
    std::string class_prefix = "java::DerivedGenericInst";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const class_typet &derived_class_type =
      require_type::require_java_non_generic_class(derived_symbol.type);

    // TODO: Currently we do not support extracting information
    // about the base classes generic information - issue TG-1287
  }
}

SCENARIO(
  "parse_derived_generic_class_uninst",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "DerivedGenericUninst", "./java_bytecode/java_bytecode_parse_generics");

  THEN("There should be a symbol for the DerivedGenericUninst class")
  {
    std::string class_prefix = "java::DerivedGenericUninst";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const java_generic_class_typet &derived_class_type =
      require_type::require_java_generic_class(
        derived_symbol.type, {class_prefix + "::T"});

    // TODO: Currently we do not support extracting information
    // about the base classes generic information - issue TG-1287
  }
}
