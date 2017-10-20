/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/require_symbol.h>
#include <testing-utils/require_type.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/language.h>
#include <util/prefix.h>
#include <util/std_types.h>

#include <java_bytecode/java_bytecode_language.h>

#include <iostream>
#include <testing-utils/load_java_class.h>

SCENARIO(
  "java_bytecode_parse_generic_inner_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericClass", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericClass";
  THEN("There should be a symbol for GenericClass")
  {
    REQUIRE(new_symbol_table.has_symbol(class_prefix));
    const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &class_type =
      require_symbol::require_complete_class(class_symbol);

    THEN("The field component should be a pointer to GenericClass$InnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field");

      require_type::require_pointer(
        field_component.type(), symbol_typet("java::GenericClass$InnerClass"));
    }
  }
}
