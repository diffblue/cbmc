/*******************************************************************\

 Module: Unit tests for generating new type with generic parameters
         substitued for concrete types

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>

#include <util/symbol_table.h>

#include <java_bytecode/generate_java_generic_type.h>
#include <testing-utils/require_type.h>
#include <testing-utils/generic_utils.h>
#include <util/ui_message.h>

/// Helper function to specalise a generic class from a named component of a
/// named class
/// \param class_name: The name of the class that has a generic component.
/// \param component_name: The name of the generic component
/// \param new_symbol_table: The symbol table to use.
void specialise_generic_from_component(
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

SCENARIO(
  "generate_java_generic_type_from_file",
  "[core][java_bytecode][generate_java_generic_type]")
{
  auto expected_symbol=
    "java::generic_two_fields$bound_element<java::java.lang.Integer>";

  GIVEN("A generic java type with two generic fields and a concrete "
          "substitution")
  {
    symbol_tablet new_symbol_table=
      load_java_class("generic_two_fields",
                      "./java_bytecode/generate_concrete_generic_type");

    specialise_generic_from_component(
      "java::generic_two_fields", "belem", new_symbol_table);

    REQUIRE(new_symbol_table.has_symbol(expected_symbol));
    THEN("The class should contain two instantiated fields.")
    {
      const auto &class_symbol=new_symbol_table.lookup(
        "java::generic_two_fields$bound_element<java::java.lang.Integer>");
      const typet &symbol_type=class_symbol->type;

      REQUIRE(symbol_type.id()==ID_struct);
      class_typet class_type=to_class_type(symbol_type);
      REQUIRE(class_type.is_class());

      REQUIRE(class_type.has_component("first"));
      const auto &first_component=class_type.get_component("first");
      REQUIRE(is_java_generic_inst_parameter(first_component.type()));
      REQUIRE(first_component.type().id()==ID_pointer);
      REQUIRE(first_component.type().subtype().id()==ID_symbol);
      REQUIRE(to_symbol_type(
        first_component.type().subtype()).get_identifier()==
          "java::java.lang.Integer");
      REQUIRE(class_type.has_component("second"));
      const auto &second_component=class_type.get_component("second");
      REQUIRE(is_java_generic_inst_parameter(second_component.type()));
      REQUIRE(second_component.type().id()==ID_pointer);
      REQUIRE(second_component.type().subtype().id()==ID_symbol);
      REQUIRE(to_symbol_type(
        second_component.type().subtype()).get_identifier()==
          "java::java.lang.Integer");
    }
  }
}


SCENARIO(
  "generate_java_generic_type_from_file_two_params",
  "[core][java_bytecode][generate_java_generic_type]")
{
  auto expected_symbol=
    "java::generic_two_parameters$KeyValuePair"
      "<java::java.lang.String,"
      "java::java.lang.Integer>";

  GIVEN("A generic java type with two generic parameters, like a Hashtable")
  {
    symbol_tablet new_symbol_table=
      load_java_class("generic_two_parameters",
                      "./java_bytecode/generate_concrete_generic_type");

    specialise_generic_from_component(
      "java::generic_two_parameters", "bomb", new_symbol_table);

    REQUIRE(new_symbol_table.has_symbol(
      "java::generic_two_parameters$KeyValuePair"));
    THEN("The class should have two subtypes in the vector of the types of "
           "the generic components.")
    {
      const auto &class_symbol=new_symbol_table.lookup(
        expected_symbol);
      const typet &symbol_type=class_symbol->type;

      REQUIRE(symbol_type.id()==ID_struct);
      class_typet class_type=to_class_type(symbol_type);
      REQUIRE(class_type.is_class());

      REQUIRE(class_type.has_component("key"));
      const auto &first_component=class_type.get_component("key");
      REQUIRE(is_java_generic_inst_parameter(first_component.type()));
      REQUIRE(class_type.has_component("value"));
      const auto &second_component=class_type.get_component("value");
      REQUIRE(is_java_generic_inst_parameter(second_component.type()));
    }
  }
}

SCENARIO(
  "generate_java_generic_type_from_file_two_instances",
  "[core][java_bytecode][generate_java_generic_type]")
{
  // After we have loaded the class and converted the generics,
  // the presence of these two symbols in the symbol table is
  // proof enough that we did the work we needed to do correctly.
  auto first_expected_symbol=
    "java::generic_two_instances$element<java::java.lang.Boolean>";
  auto second_expected_symbol=
    "java::generic_two_instances$element<java::java.lang.Integer>";

  GIVEN("A generic java type with a field that refers to another generic with"
          " an uninstantiated parameter.")
  {
    symbol_tablet new_symbol_table=
      load_java_class("generic_two_instances",
                      "./java_bytecode/generate_concrete_generic_type");

    specialise_generic_from_component(
      "java::generic_two_instances", "bool_element", new_symbol_table);
    specialise_generic_from_component(
      "java::generic_two_instances", "int_element", new_symbol_table);

    REQUIRE(new_symbol_table.has_symbol(first_expected_symbol));
    auto first_symbol=new_symbol_table.lookup(first_expected_symbol);
    REQUIRE(first_symbol->type.id()==ID_struct);
    const struct_union_typet::componentt &component =
      require_type::require_component(
        to_struct_type(first_symbol->type), "elem");
    auto first_symbol_type=component.type();
    require_type::require_pointer(
      first_symbol_type, symbol_typet("java::java.lang.Boolean"));

    REQUIRE(new_symbol_table.has_symbol(second_expected_symbol));
    auto second_symbol=new_symbol_table.lookup(second_expected_symbol);
    REQUIRE(second_symbol->type.id()==ID_struct);
    const struct_union_typet::componentt &second_component =
      require_type::require_component(
        to_struct_type(second_symbol->type), "elem");
    auto second_symbol_type=second_component.type();
    require_type::require_pointer(
      second_symbol_type, symbol_typet("java::java.lang.Integer"));
  }
}

SCENARIO(
  "generate_java_generic_type_with_array_concrete_type",
  "[core][java_bytecode][generate_java_generic_type]")
{
  // We have a 'harness' class who's only purpose is to contain a reference
  // to the generic class so that we can test the specialization of that generic
  // class
  const irep_idt harness_class = "java::generic_field_array_instantiation";

  // We want to test that the specialized/instantiated class has it's field
  // type updated, so find the specialized class, not the generic class.
  const irep_idt test_class =
    "java::generic_field_array_instantiation$generic<java::array[reference]"
    "of_java::java.lang.Float>";

  GIVEN("A generic type instantiated with an array type")
  {
    symbol_tablet new_symbol_table = load_java_class(
      "generic_field_array_instantiation",
      "./java_bytecode/generate_concrete_generic_type");

    // Ensure the class has been specialized
    REQUIRE(new_symbol_table.has_symbol(harness_class));
    const symbolt &harness_symbol = new_symbol_table.lookup_ref(harness_class);

    const struct_typet::componentt &harness_component =
      require_type::require_component(to_struct_type(harness_symbol.type), "f");

    ui_message_handlert message_handler;
    generate_java_generic_typet instantiate_generic_type(message_handler);
    instantiate_generic_type(
      to_java_generic_type(harness_component.type()), new_symbol_table);

    // Test the specialized class
    REQUIRE(new_symbol_table.has_symbol(test_class));
    const symbolt test_class_symbol = new_symbol_table.lookup_ref(test_class);

    REQUIRE(test_class_symbol.type.id() == ID_struct);
    const struct_typet::componentt &field_component =
      require_type::require_component(
        to_struct_type(test_class_symbol.type), "gf");
    const typet &test_field_type = field_component.type();

    REQUIRE(test_field_type.id() == ID_pointer);
    REQUIRE(test_field_type.subtype().id() == ID_symbol);
    const symbol_typet test_field_array =
      to_symbol_type(test_field_type.subtype());
    REQUIRE(test_field_array.get_identifier() == "java::array[reference]");
    const pointer_typet &element_type = require_type::require_pointer(
      java_array_element_type(test_field_array),
      symbol_typet("java::java.lang.Float"));

    // check for other specialized classes, in particular different symbol ids
    // for arrays with different element types
    GIVEN("A generic type instantiated with different array types")
    {
      const irep_idt test_class_integer =
        "java::generic_field_array_instantiation$generic<java::array[reference]"
        "of_"
        "java::java.lang.Integer>";

      const irep_idt test_class_int =
        "java::generic_field_array_instantiation$generic<java::array[int]>";

      const irep_idt test_class_float =
        "java::generic_field_array_instantiation$generic<java::array[float]>";

      const struct_typet::componentt &component_g =
        require_type::require_component(
          to_struct_type(harness_symbol.type), "g");
      instantiate_generic_type(
        to_java_generic_type(component_g.type()), new_symbol_table);
      REQUIRE(new_symbol_table.has_symbol(test_class_integer));

      const struct_typet::componentt &component_h =
        require_type::require_component(
          to_struct_type(harness_symbol.type), "h");
      instantiate_generic_type(
        to_java_generic_type(component_h.type()), new_symbol_table);
      REQUIRE(new_symbol_table.has_symbol(test_class_int));

      const struct_typet::componentt &component_i =
        require_type::require_component(
          to_struct_type(harness_symbol.type), "i");
      instantiate_generic_type(
        to_java_generic_type(component_i.type()), new_symbol_table);
      REQUIRE(new_symbol_table.has_symbol(test_class_float));
    }
  }
}

SCENARIO(
  "generate_java_generic_type with a generic array field",
  "[core][java_bytecode][generate_java_generic_type]")
{
  const irep_idt harness_class = "java::generic_field_array_instantiation";
  GIVEN("A generic class with a field of type T []")
  {
    symbol_tablet new_symbol_table = load_java_class(
      "generic_field_array_instantiation",
      "./java_bytecode/generate_concrete_generic_type");

    const irep_idt inner_class = "genericArray";

    WHEN("We specialise that class from a reference to it")
    {
      specialise_generic_from_component(
        harness_class, "genericArrayField", new_symbol_table);
      THEN(
        "There should be a specialised version of the class in the symbol "
        "table")
      {
        const irep_idt specialised_class_name = id2string(harness_class) + "$" +
                                                id2string(inner_class) +
                                                "<java::java.lang.Float>";
        REQUIRE(new_symbol_table.has_symbol(specialised_class_name));

        const symbolt test_class_symbol =
          new_symbol_table.lookup_ref(specialised_class_name);

        REQUIRE(test_class_symbol.type.id() == ID_struct);
        THEN("The array field should be specialised to be an array of floats")
        {
          const struct_typet::componentt &field_component =
            require_type::require_component(
              to_struct_type(test_class_symbol.type), "arrayField");

          const pointer_typet &component_pointer_type =
            require_type::require_pointer(field_component.type(), {});

          const symbol_typet &pointer_subtype = require_type::require_symbol(
            component_pointer_type.subtype(), "java::array[reference]");

          const typet &array_type = java_array_element_type(pointer_subtype);

          require_type::require_pointer(
            array_type, symbol_typet("java::java.lang.Float"));
        }

        THEN(
          "The generic class field should be specialised to be a generic "
          "class with the appropriate type")
        {
          const struct_typet::componentt &field_component =
            require_type::require_component(
              to_struct_type(test_class_symbol.type), "genericClassField");

          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_parameter_kindt::Inst,
              "java::java.lang.Float"}});
        }
      }
    }
    WHEN(
      "We specialise the class with an array we should have appropriate types")
    {
      specialise_generic_from_component(
        harness_class, "genericArrayArrayField", new_symbol_table);
      THEN(
        "There should be a specialised version of the class in the symbol "
        "table")
      {
        const std::string specialised_string =
          "<java::array[reference]of_"
          "java::java.lang.Float>";
        const irep_idt specialised_class_name = id2string(harness_class) + "$" +
                                                id2string(inner_class) +
                                                specialised_string;

        REQUIRE(new_symbol_table.has_symbol(specialised_class_name));

        const symbolt test_class_symbol =
          new_symbol_table.lookup_ref(specialised_class_name);

        REQUIRE(test_class_symbol.type.id() == ID_struct);
        THEN("The array field should be specialised to be an array of floats")
        {
          const struct_typet::componentt &field_component =
            require_type::require_component(
              to_struct_type(test_class_symbol.type), "arrayField");

          const pointer_typet &component_pointer_type =
            require_type::require_pointer(field_component.type(), {});

          const symbol_typet &pointer_subtype = require_type::require_symbol(
            component_pointer_type.subtype(), "java::array[reference]");

          const typet &array_type = java_array_element_type(pointer_subtype);

          require_type::require_pointer(
            array_type, symbol_typet("java::array[reference]"));

          const typet &array_subtype =
            java_array_element_type(to_symbol_type(array_type.subtype()));

          require_type::require_pointer(
            array_subtype, symbol_typet("java::java.lang.Float"));
        }

        THEN(
          "The generic class field should be specialised to be a generic "
          "class with the appropriate type")
        {
          const struct_typet::componentt &field_component =
            require_type::require_component(
              to_struct_type(test_class_symbol.type), "genericClassField");

          const java_generic_typet &param_type =
            require_type::require_java_generic_type(
              field_component.type(),
              {{require_type::type_parameter_kindt::Inst,
                "java::array[reference]"}});

          const typet &array_type = java_array_element_type(
            to_symbol_type(param_type.generic_type_variables()[0].subtype()));
          require_type::require_pointer(
            array_type, symbol_typet("java::java.lang.Float"));
        }
      }
    }
  }
}
