/*******************************************************************\

 Module: Unit tests for generating new type with generic parameters
         substitued for concrete types

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>

#include <util/symbol_table.h>

#include <java_bytecode/generate_java_generic_type.h>


SCENARIO(
  "generate_java_generic_type_from_file",
  "[core][java_bytecode][generate_java_generic_type]")
{
  auto expected_symbol=
    "java::generic_two_fields$bound_element<java::java.lang.Integer>";

  GIVEN("A generic java type with two generic fields and a concrete "
          "substitution")
  {
    concrete_symbol_tablet new_symbol_table=
      load_java_class("generic_two_fields",
                      "./java_bytecode/generate_concrete_generic_type");

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
    concrete_symbol_tablet new_symbol_table=
      load_java_class("generic_two_parameters",
                      "./java_bytecode/generate_concrete_generic_type");

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
  "generate_java_generic_type_from_file_uninstantiated_param",
  "[core][java_bytecode][generate_java_generic_type]")
{
  GIVEN("A generic java type with a field that refers to another generic with"
          " an uninstantiated parameter.")
  {
    concrete_symbol_tablet new_symbol_table=
      load_java_class("generic_unknown_field",
                      "./java_bytecode/generate_concrete_generic_type");

    // It's illegal to create an instantiation of a field that refers
    // to a (still) uninstantiated generic class, so this is checking that
    // this hasn't happened.
    REQUIRE_FALSE(new_symbol_table.has_symbol
      ("java::generic_unknown_field$element<T>"));
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
    concrete_symbol_tablet new_symbol_table=
      load_java_class("generic_two_instances",
                      "./java_bytecode/generate_concrete_generic_type");

    REQUIRE(new_symbol_table.has_symbol(first_expected_symbol));
    auto first_symbol=new_symbol_table.lookup(first_expected_symbol);
    REQUIRE(first_symbol->type.id()==ID_struct);
    auto first_symbol_type=
      to_struct_type(first_symbol->type).components()[3].type();
    REQUIRE(first_symbol_type.id()==ID_pointer);
    REQUIRE(first_symbol_type.subtype().id()==ID_symbol);
    REQUIRE(to_symbol_type(first_symbol_type.subtype()).get_identifier()==
      "java::java.lang.Boolean");

    REQUIRE(new_symbol_table.has_symbol(second_expected_symbol));
    auto second_symbol=new_symbol_table.lookup(second_expected_symbol);
    REQUIRE(second_symbol->type.id()==ID_struct);
    auto second_symbol_type=
      to_struct_type(second_symbol->type).components()[3].type();
    REQUIRE(second_symbol_type.id()==ID_pointer);
    REQUIRE(second_symbol_type.subtype().id()==ID_symbol);
    REQUIRE(to_symbol_type(second_symbol_type.subtype()).get_identifier()==
            "java::java.lang.Integer");
  }
}
