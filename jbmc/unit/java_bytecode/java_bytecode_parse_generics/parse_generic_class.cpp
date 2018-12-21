/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_generic_class_one_param",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table =
    load_java_class("Generic", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::Generic";

  WHEN("Parsing the class")
  {
    THEN("There is a generic class symbol Generic")
    {
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
      const java_generic_class_typet &java_generic_class =
        require_type::require_complete_java_generic_class(
          class_symbol.type, {class_prefix + "::T"});

      const struct_typet class_struct = to_struct_type(class_symbol.type);
      THEN("It has field t")
      {
        const struct_union_typet::componentt &field_t =
          require_type::require_component(class_struct, "t");

        THEN("It is the generic parameter T")
        {
          require_type::require_java_generic_parameter(
            field_t.type(), class_prefix + "::T");
        }
      }

      THEN("It has field g pointing to Generic")
      {
        const struct_union_typet::componentt &field_g =
          require_type::require_component(class_struct, "g");
        require_type::require_pointer(
          field_g.type(), struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            field_g.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }
}

SCENARIO(
  "parse_generic_class_two_param",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericTwoParam", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericTwoParam";

  WHEN("Parsing the class")
  {
    THEN("There is a generic class symbol GenericTwoParam")
    {
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
      const java_generic_class_typet &java_generic_class =
        require_type::require_complete_java_generic_class(
          class_symbol.type, {class_prefix + "::T", class_prefix + "::U"});

      const struct_typet class_struct = to_struct_type(class_symbol.type);
      THEN("It has field t")
      {
        const struct_union_typet::componentt &field_t =
          require_type::require_component(class_struct, "t");

        THEN("It is the generic parameter T")
        {
          require_type::require_java_generic_parameter(
            field_t.type(), class_prefix + "::T");
        }
      }
      THEN("It has field u")
      {
        const struct_union_typet::componentt &field_u =
          require_type::require_component(class_struct, "u");

        THEN("It is the generic parameter U")
        {
          require_type::require_java_generic_parameter(
            field_u.type(), class_prefix + "::U");
        }
      }
    }
  }
}
