/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_generic_array_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericArray", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericArray";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
  const java_generic_class_typet &java_generic_class =
    require_type::require_complete_java_generic_class(
      class_symbol.type, {class_prefix + "::T"});

  THEN("There should be field t")
  {
    const struct_union_typet::componentt &field_t =
      require_type::require_component(java_generic_class, "t");

    THEN("It is an array")
    {
      const pointer_typet &field_t_pointer = require_type::require_pointer(
        field_t.type(), struct_tag_typet("java::array[reference]"));

      const struct_tag_typet &field_t_subtype =
        to_struct_tag_type(field_t_pointer.subtype());
      const struct_typet &subtype_type = to_struct_type(
        new_symbol_table.lookup_ref(field_t_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_type));

      THEN("The elements have the parametric type T")
      {
        const typet &element = java_array_element_type(field_t_subtype);
        require_type::require_java_generic_parameter(
          element, class_prefix + "::T");
      }
    }
  }

  THEN("There should be field t2")
  {
    const struct_union_typet::componentt &field_t2 =
      require_type::require_component(java_generic_class, "t2");

    THEN("It is an array")
    {
      const pointer_typet &field_t2_pointer = require_type::require_pointer(
        field_t2.type(), struct_tag_typet("java::array[reference]"));

      const struct_tag_typet &field_t2_subtype =
        to_struct_tag_type(field_t2_pointer.subtype());
      const struct_typet &subtype_struct = to_struct_type(
        new_symbol_table.lookup_ref(field_t2_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_struct));

      THEN("The elements have type Generic<T>")
      {
        const typet &element = java_array_element_type(field_t2_subtype);
        require_type::require_pointer(
          element, struct_tag_typet("java::Generic"));
        require_type::require_java_generic_type(
          element,
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }
  }

  THEN("There should be field t3")
  {
    const struct_union_typet::componentt &field_t3 =
      require_type::require_component(java_generic_class, "t3");

    THEN("It is an array")
    {
      const pointer_typet &field_t3_pointer = require_type::require_pointer(
        field_t3.type(), struct_tag_typet("java::array[reference]"));

      const struct_tag_typet &field_t3_subtype =
        to_struct_tag_type(field_t3_pointer.subtype());
      const struct_typet &subtype_struct = to_struct_type(
        new_symbol_table.lookup_ref(field_t3_subtype.get_identifier()).type);
      REQUIRE(is_valid_java_array(subtype_struct));

      THEN("The elements have type Generic<Integer>")
      {
        const typet &element = java_array_element_type(field_t3_subtype);
        require_type::require_pointer(
          element, struct_tag_typet("java::Generic"));
        require_type::require_java_generic_type(
          element,
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
    }
  }
}
