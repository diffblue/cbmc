/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>
#include <testing-utils/require_symbol.h>


#include <util/config.h>
#include <util/language.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO(
  "parse_generic_array_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericArray", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericArray";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
  const class_typet &class_type =
    require_symbol::require_complete_class(class_symbol);

  THEN("There should be field t")
  {
    struct_union_typet::componentt field_t =
      require_type::require_component(class_type, "t");

    THEN("It is an array")
    {
      pointer_typet field_t_pointer =
        require_type::require_pointer(
          field_t.type(),
          symbol_typet("java::array[reference]"));

      const symbol_typet &field_t_subtype =
        to_symbol_type(field_t_pointer.subtype());
      const struct_typet &subtype_type = to_struct_type(
        new_symbol_table.lookup_ref(field_t_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_type));

      THEN("The elements have the parametric type T")
      {
        const typet &element = field_t_subtype.find_type(ID_C_element_type);
        REQUIRE(is_java_generic_parameter(element));
        java_generic_parametert element_parameter =
          to_java_generic_parameter(element);
        REQUIRE(element_parameter.type_variable().get_identifier() ==
                class_prefix + "::T");
      }
    }
  }

  THEN("There should be field t2")
  {
    struct_union_typet::componentt field_t2 =
      require_type::require_component(class_type, "t2");

    THEN("It is an array")
    {
      pointer_typet field_t2_pointer =
        require_type::require_pointer(
          field_t2.type(),
          symbol_typet("java::array[reference]"));

      const symbol_typet &field_t2_subtype =
        to_symbol_type(field_t2_pointer.subtype());
      const struct_typet &subtype_struct = to_struct_type(
        new_symbol_table.lookup_ref(field_t2_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_struct));

      THEN("The elements have type Generic<T>")
      {
        const typet &element = field_t2_subtype.find_type(ID_C_element_type);
        REQUIRE(is_java_generic_type(element));
        const java_generic_typet generic_element =
          to_java_generic_type(element);
        require_type::require_pointer(
          generic_element, symbol_typet
            ("java::Generic"));

        REQUIRE(is_java_generic_parameter(
          generic_element.generic_type_variables().front()));
        java_generic_parametert parameter =
          generic_element.generic_type_variables().front();
        REQUIRE(parameter.type_variable().get_identifier() ==
                class_prefix + "::T");
      }
    }
  }

  THEN("There should be field t3")
  {
    struct_union_typet::componentt field_t3 =
      require_type::require_component(class_type, "t3");

    THEN("It is an array")
    {
      pointer_typet field_t3_pointer =
        require_type::require_pointer(
          field_t3.type(),
          symbol_typet("java::array[reference]"));

      const symbol_typet &field_t3_subtype =
        to_symbol_type(field_t3_pointer.subtype());
      const struct_typet &subtype_struct = to_struct_type(
        new_symbol_table.lookup_ref(field_t3_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_struct));

      THEN("The elements have type Generic<Integer>")
      {
        const typet &element = field_t3_subtype.find_type(ID_C_element_type);
        REQUIRE(is_java_generic_type(element));
        const java_generic_typet generic_element =
          to_java_generic_type(element);
        require_type::require_pointer(
          generic_element, symbol_typet("java::Generic"));

        REQUIRE(is_java_generic_inst_parameter(
          generic_element.generic_type_variables().front()));
        java_generic_parametert parameter =
          generic_element.generic_type_variables().front();
        require_type::require_pointer(
          parameter, symbol_typet("java::java.lang.Integer"));
      }
    }
  }
}
