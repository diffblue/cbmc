/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_symbol.h>
#include <testing-utils/require_type.h>

#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO(
  "parse_bounded_generic_inner_classes",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "BoundedGenericInnerClasses",
    "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::BoundedGenericInnerClasses";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  WHEN("Parsing an inner class with type variable")
  {
    std::string inner_name = class_prefix + "$Inner";
    REQUIRE(new_symbol_table.has_symbol(inner_name));
    THEN("The symbol type should be generic")
    {
      const symbolt &class_symbol = new_symbol_table.lookup_ref(inner_name);
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_generics_class_typet java_generics_class_type =
        require_type::require_java_generic_class(class_type);

      const typet &elem_type =
        to_java_class_type(class_type).component_type("elem");
      REQUIRE(is_java_generic_parameter(elem_type));

      REQUIRE(java_generics_class_type.generic_types().size() == 1);
      THEN("Type variable is named 'E'")
      {
        typet &type_var = java_generics_class_type.generic_types().front();
        REQUIRE(is_java_generic_parameter(type_var));
        java_generic_parametert generic_type_var =
          to_java_generic_parameter(type_var);
        REQUIRE(
          generic_type_var.type_variable().get_identifier() ==
          inner_name + "::E");
        typet &sub_type = generic_type_var.subtype();
        REQUIRE(sub_type.id() == ID_symbol);
        symbol_typet &bound_type = to_symbol_type(sub_type);
        REQUIRE(bound_type.get_identifier() == "java::java.lang.Object");
      }
    }
  }

  WHEN("Parsing an inner class with bounded type variable")
  {
    std::string boundedinner_name = class_prefix + "$BoundedInner";
    REQUIRE(new_symbol_table.has_symbol(boundedinner_name));
    THEN("The symbol type should be generic")
    {
      const symbolt &class_symbol =
        new_symbol_table.lookup_ref(boundedinner_name);
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_generics_class_typet java_generics_class_type =
        require_type::require_java_generic_class(class_type);

      REQUIRE(java_generics_class_type.generic_types().size() == 1);
      typet &type_var = java_generics_class_type.generic_types().front();
      REQUIRE(is_java_generic_parameter(type_var));
      java_generic_parametert generic_type_var =
        to_java_generic_parameter(type_var);

      REQUIRE(
        generic_type_var.type_variable().get_identifier() ==
        boundedinner_name + "::NUM");
      REQUIRE(
        java_generics_class_type_var(0, java_generics_class_type) ==
        boundedinner_name + "::NUM");
      THEN("Bound must be Number")
      {
        typet &sub_type = generic_type_var.subtype();
        REQUIRE(sub_type.id() == ID_symbol);
        symbol_typet &bound_type = to_symbol_type(sub_type);
        REQUIRE(bound_type.get_identifier() == "java::java.lang.Number");
        REQUIRE(
          to_symbol_type(
            java_generics_class_type_bound(0, java_generics_class_type))
            .get_identifier() == "java::java.lang.Number");
      }

      const typet &elem_type =
        to_java_class_type(class_type).component_type("elem");
      REQUIRE(is_java_generic_parameter(elem_type));
    }
  }

  WHEN("There is a generic field with a concrete type")
  {
    const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
    class_typet class_type =
      require_symbol::require_complete_class(class_symbol);

    java_class_typet java_class_type = to_java_class_type(class_type);
    REQUIRE(!is_java_generics_class_type(java_class_type));

    const typet &belem_type = java_class_type.component_type("belem");

    REQUIRE(belem_type != nil_typet());
    REQUIRE(is_java_generic_type(belem_type));
    THEN("Field has instantiated type variable")
    {
      const java_generic_typet &container = to_java_generic_type(belem_type);

      const std::vector<java_generic_parametert> &generic_types =
        container.generic_type_variables();
      REQUIRE(generic_types.size() == 1);

      const typet &inst_type = java_generic_get_inst_type(0, container);

      REQUIRE(inst_type.id() == ID_pointer);
      const typet &inst_type_symbol = inst_type.subtype();
      REQUIRE(inst_type_symbol.id() == ID_symbol);
      REQUIRE(
        to_symbol_type(inst_type_symbol).get_identifier() ==
        "java::java.lang.Integer");
    }
  }

  WHEN("Parsing an inner class with double bounded type variable")
  {
    std::string doubleboundedinner_name = class_prefix + "$DoubleBoundedInner";
    REQUIRE(new_symbol_table.has_symbol(doubleboundedinner_name));
    THEN("The bounds should be encoded")
    {
      const symbolt &class_symbol =
        new_symbol_table.lookup_ref(doubleboundedinner_name);
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);

      java_class_typet java_class_type = to_java_class_type(class_type);
      REQUIRE_FALSE(is_java_generics_class_type(java_class_type));

// TODO (tkiley): Extend this unit test when bounds are correctly
// parsed - issue TG-1286
#if 0
      java_generics_class_typet java_generics_class_type=
        to_java_generics_class_type(java_class_type);
      REQUIRE(java_generics_class_type.generic_types().size()==1);
      typet &type_var=java_generics_class_type.generic_types().front();
      REQUIRE(is_java_generic_parameter(type_var));
      java_generic_parametert generic_type_var=
        to_java_generic_parameter(type_var);

      REQUIRE(
        generic_type_var.type_variable().get_identifier()==
        doubleboundedinner_name+"::T");
      REQUIRE(
        java_generics_class_type_var(0, java_generics_class_type)==
        doubleboundedinner_name+"::T");
      THEN("Bound must be Number and Interface")
      {

      }
#endif
    }
  }

  GIVEN("An inner class with multiple generic parameters")
  {
    std::string twoelementinner_name = class_prefix + "$TwoElementInner";
    REQUIRE(new_symbol_table.has_symbol(twoelementinner_name));
    THEN("Both generic parameters should be encoded")
    {
      const symbolt &class_symbol =
        new_symbol_table.lookup_ref(twoelementinner_name);
      class_typet class_type =
        require_symbol::require_complete_class(class_symbol);
      java_generics_class_typet java_generics_class_type =
        require_type::require_java_generic_class(class_type);

      REQUIRE(java_generics_class_type.generic_types().size() == 2);

      // The first parameter should be called K
      {
        const typet first_param =
          java_generics_class_type.generic_types().at(0);
        REQUIRE(is_java_generic_parameter(first_param));
        java_generic_parametert generic_type_var =
          to_java_generic_parameter(first_param);

        REQUIRE(
          generic_type_var.type_variable().get_identifier() ==
          twoelementinner_name + "::K");
        REQUIRE(
          java_generics_class_type_var(0, java_generics_class_type) ==
          twoelementinner_name + "::K");
      }

      // The second parameter should be called V
      {
        const typet &second_param =
          java_generics_class_type.generic_types().at(1);
        REQUIRE(is_java_generic_parameter(second_param));
        java_generic_parametert generic_type_var =
          to_java_generic_parameter(second_param);

        REQUIRE(
          generic_type_var.type_variable().get_identifier() ==
          twoelementinner_name + "::V");
        REQUIRE(
          java_generics_class_type_var(1, java_generics_class_type) ==
          twoelementinner_name + "::V");
      }
    }
  }
}
