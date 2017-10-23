/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_symbol.h>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO(
  "java_bytecode_parse_generic_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table =
    load_java_class("Generic", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::Generic";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  WHEN("Parsing the class")
  {
    REQUIRE(new_symbol_table.has_symbol(class_prefix));
    THEN("The class symbol is generic")
    {
      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_class_typet java_class_type = to_java_class_type(class_type);

      REQUIRE(is_java_generics_class_type(java_class_type));
      java_generics_class_typet java_generics_class_type =
        to_java_generics_class_type(java_class_type);

      THEN("The type variable is T")
      {
        REQUIRE(java_generics_class_type.generic_types().size()==1);
        typet &type_var=java_generics_class_type.generic_types().front();
        REQUIRE(is_java_generic_parameter(type_var));
        java_generic_parametert generic_type_var=
          to_java_generic_parameter(type_var);
        REQUIRE(
          generic_type_var.type_variable().get_identifier() ==
          class_prefix + "::T");
        typet &sub_type = generic_type_var.subtype();
        REQUIRE(sub_type.id() == ID_symbol);
        symbol_typet &bound_type = to_symbol_type(sub_type);
        REQUIRE(bound_type.get_identifier() == "java::java.lang.Object");
      }
    }
  }
}
