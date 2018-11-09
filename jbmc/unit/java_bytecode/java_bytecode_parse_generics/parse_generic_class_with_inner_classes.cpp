/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_generic_class_with_inner_classes",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericClassWithInnerClasses",
    "./java_bytecode/java_bytecode_parse_generics");

  std::string outer_class_prefix = "java::GenericClassWithInnerClasses";

  WHEN("Generic outer class has fields which are objects of the inner classes")
  {
    REQUIRE(new_symbol_table.has_symbol(outer_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(outer_class_prefix);
    const java_generic_class_typet &generic_class =
      require_type::require_complete_java_generic_class(
        class_symbol.type, {outer_class_prefix + "::T"});
    THEN("There is a field f1 of generic type with correct arguments")
    {
      const auto &field = require_type::require_component(generic_class, "f1");
      require_type::require_pointer(
        field.type(), struct_tag_typet(outer_class_prefix + "$Inner"));
      require_type::require_java_generic_type(
        field.type(),
        {{require_type::type_argument_kindt::Var, outer_class_prefix + "::T"}});
    }
    THEN("There is a field f2 of generic type with correct arguments")
    {
      const auto &field = require_type::require_component(generic_class, "f2");
      require_type::require_pointer(
        field.type(),
        struct_tag_typet(outer_class_prefix + "$Inner$InnerInner"));
      require_type::require_java_generic_type(
        field.type(),
        {{require_type::type_argument_kindt::Var, outer_class_prefix + "::T"}});
    }
    THEN("There is a field f3 of generic type with correct arguments")
    {
      const auto &field = require_type::require_component(generic_class, "f3");
      require_type::require_pointer(
        field.type(), struct_tag_typet(outer_class_prefix + "$GenericInner"));
      require_type::require_java_generic_type(
        field.type(),
        {{require_type::type_argument_kindt::Var, outer_class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});
    }
  }

  WHEN("Inner class of a generic outer class is parsed")
  {
    std::string inner_class_prefix = outer_class_prefix + "$Inner";
    REQUIRE(new_symbol_table.has_symbol(inner_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(inner_class_prefix);

    THEN("It has correct implicit generic types")
    {
      const java_implicitly_generic_class_typet &java_class =
        require_type::require_complete_java_implicitly_generic_class(
          class_symbol.type, {outer_class_prefix + "::T"});

      THEN(
        "There is a field t1 which is the generic parameter of the outer "
        "class")
      {
        const auto &field = require_type::require_component(java_class, "t1");
        require_type::require_java_generic_parameter(
          field.type(), outer_class_prefix + "::T");
      }
      THEN(
        "There is a field t2 of generic type with the generic "
        "parameter of the outer class")
      {
        const auto &field = require_type::require_component(java_class, "t2");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        require_type::require_java_generic_type(
          field.type(),
          {{require_type::type_argument_kindt::Var,
            outer_class_prefix + "::T"}});
      }
    }
  }

  WHEN("Inner class of an inner class of a generic outer class is parsed")
  {
    std::string inner_inner_class_prefix =
      outer_class_prefix + "$Inner$InnerInner";
    REQUIRE(new_symbol_table.has_symbol(inner_inner_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(inner_inner_class_prefix);

    THEN("It has correct implicit generic types")
    {
      const java_implicitly_generic_class_typet &java_class =
        require_type::require_complete_java_implicitly_generic_class(
          class_symbol.type, {outer_class_prefix + "::T"});

      THEN(
        "There is a field tt1 which is the generic parameter of the outer "
        "class")
      {
        const auto &field = require_type::require_component(java_class, "tt1");
        require_type::require_java_generic_parameter(
          field.type(), outer_class_prefix + "::T");
      }
      THEN(
        "There is a field tt2 of nested generic type with the generic "
        "parameter of the outer class")
      {
        const auto &field = require_type::require_component(java_class, "tt2");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument =
          generic_field.generic_type_arguments().at(0);
        const java_generic_typet generic_type_argument =
          require_type::require_java_generic_type(
            type_argument,
            {{require_type::type_argument_kindt::Var,
              outer_class_prefix + "::T"}});
      }
    }
  }

  WHEN("Generic inner class of a generic outer class is parsed")
  {
    std::string generic_inner_class_prefix =
      outer_class_prefix + "$GenericInner";
    REQUIRE(new_symbol_table.has_symbol(generic_inner_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(generic_inner_class_prefix);

    THEN("It has correct generic types and implicit generic types")
    {
      require_type::require_complete_java_implicitly_generic_class(
        class_symbol.type, {outer_class_prefix + "::T"});
      const java_generic_class_typet &generic_class =
        require_type::require_complete_java_generic_class(
          class_symbol.type, {generic_inner_class_prefix + "::U"});

      THEN(
        "There is a field gt1 which is the generic parameter of the outer "
        "class")
      {
        const auto &field =
          require_type::require_component(generic_class, "gt1");
        require_type::require_java_generic_parameter(
          field.type(), outer_class_prefix + "::T");
      }
      THEN(
        "There is a field gt2 of generic type with the generic "
        "parameter of the outer class")
      {
        const auto &field =
          require_type::require_component(generic_class, "gt2");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        require_type::require_java_generic_type(
          field.type(),
          {{require_type::type_argument_kindt::Var,
             outer_class_prefix + "::T"},
           {require_type::type_argument_kindt::Var,
             generic_inner_class_prefix + "::U"}});
      }
    }
  }

  WHEN(
    "A generic inner class of a generic inner class of a generic outer class "
    "is parsed")
  {
    std::string generic_inner_inner_class_prefix =
      outer_class_prefix + "$GenericInner$GenericInnerInner";
    REQUIRE(new_symbol_table.has_symbol(generic_inner_inner_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(generic_inner_inner_class_prefix);

    THEN("It has correct generic types and implicit generic types")
    {
      require_type::require_complete_java_implicitly_generic_class(
        class_symbol.type,
        {outer_class_prefix + "::T", outer_class_prefix + "$GenericInner::U"});
      require_type::require_complete_java_generic_class(
        class_symbol.type, {generic_inner_inner_class_prefix + "::V"});
    }
  }

  WHEN("A static generic inner class of a generic class is parsed")
  {
    std::string static_inner_class_prefix = outer_class_prefix + "$StaticInner";
    REQUIRE(new_symbol_table.has_symbol(static_inner_class_prefix));
    const symbolt &class_symbol =
      new_symbol_table.lookup_ref(static_inner_class_prefix);

    THEN("It has correct generic types and no implicit generic types")
    {
      REQUIRE(!is_java_implicitly_generic_class_type(class_symbol.type));
      require_type::require_complete_java_generic_class(
        class_symbol.type, {static_inner_class_prefix + "::U"});
    }
  }
}
