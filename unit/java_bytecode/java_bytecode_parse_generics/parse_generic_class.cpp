/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_symbol.h>
#include <testing-utils/require_type.h>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO(
  "java_bytecode_parse_generic_class_one_param",
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
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_generics_class_typet java_generics_class_type =
        require_type::require_java_generic_class(class_type);

      THEN("It has type variable T")
      {
        REQUIRE(java_generics_class_type.generic_types().size() == 1);
        const auto &generic_types = java_generics_class_type.generic_types();

        REQUIRE(
          generic_types[0].type_variable().get_identifier() ==
          class_prefix + "::T");
      }

      const struct_typet class_struct = to_struct_type(class_symbol.type);
      THEN("It has field t")
      {
        struct_union_typet::componentt field_t =
          require_type::require_component(class_struct, "t");

        THEN("It is the generic parameter T")
        {
          REQUIRE(is_java_generic_parameter(field_t.type()));

          const java_generic_parametert field_t_param =
            to_java_generic_parameter(field_t.type());
          REQUIRE(
            field_t_param.type_variable().get_identifier() ==
            class_prefix + "::T");
        }
      }

      THEN("It has field g pointing to Generic")
      {
        struct_union_typet::componentt field_g =
          require_type::require_component(class_struct, "g");
        require_type::require_pointer(
          field_g.type(), symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(field_g.type()));

          const java_generic_typet generic_field_g =
            to_java_generic_type(field_g.type());
          const java_generic_parametert generic_param_field_g =
            generic_field_g.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_field_g, symbol_typet("java::java.lang.Integer"));
        }
      }
    }
  }
}

SCENARIO(
  "java_bytecode_parse_generic_class_two_param",
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
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_generics_class_typet java_generics_class_type =
        require_type::require_java_generic_class(class_type);

      THEN("It has type variables T and U")
      {
        REQUIRE(java_generics_class_type.generic_types().size() == 2);
        const auto &generic_types = java_generics_class_type.generic_types();
        {
          const java_generic_parametert &generic_param = generic_types[0];
          REQUIRE(
            generic_param.type_variable().get_identifier() ==
            class_prefix + "::T");
        }
        {
          const java_generic_parametert &generic_param = generic_types[1];
          REQUIRE(
            generic_param.type_variable().get_identifier() ==
            class_prefix + "::U");
        }
      }

      const struct_typet class_struct = to_struct_type(class_symbol.type);
      THEN("It has field t")
      {
        struct_union_typet::componentt field_t =
          require_type::require_component(class_struct, "t");

        THEN("It is the generic parameter T")
        {
          REQUIRE(is_java_generic_parameter(field_t.type()));

          const java_generic_parametert field_t_param =
            to_java_generic_parameter(field_t.type());
          REQUIRE(
            field_t_param.type_variable().get_identifier() ==
            class_prefix + "::T");
        }
      }
      THEN("It has field u")
      {
        struct_union_typet::componentt field_u =
          require_type::require_component(class_struct, "u");

        THEN("It is the generic parameter U")
        {
          REQUIRE(is_java_generic_parameter(field_u.type()));

          const java_generic_parametert field_u_param =
            to_java_generic_parameter(field_u.type());
          REQUIRE(
            field_u_param.type_variable().get_identifier() ==
            class_prefix + "::U");
        }
      }
    }
  }
}
