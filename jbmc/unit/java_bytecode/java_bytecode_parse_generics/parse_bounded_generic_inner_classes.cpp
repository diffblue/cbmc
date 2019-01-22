/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

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
      require_type::require_complete_java_generic_class(
        class_symbol.type, {inner_name + "::E"});

      THEN("The fields are of correct types")
      {
        const struct_union_typet::componentt &elem =
          require_type::require_component(
            to_struct_type(class_symbol.type), "elem");
        require_type::require_java_generic_parameter(
          elem.type(), inner_name + "::E");
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
      require_type::require_complete_java_generic_class(
        class_symbol.type, {boundedinner_name + "::NUM"});

      // TODO extend when bounds are parsed correctly - TG-1286

      THEN("The fields are of correct types")
      {
        const struct_union_typet::componentt &elem =
          require_type::require_component(
            to_struct_type(class_symbol.type), "elem");
        require_type::require_java_generic_parameter(
          elem.type(), boundedinner_name + "::NUM");

        std::string method_name =
          boundedinner_name + ".f:(Ljava/lang/Number;)V";
        REQUIRE(new_symbol_table.has_symbol(method_name));
        THEN("The method parameter type should respect its bound")
        {
          const symbolt &method_symbol =
            new_symbol_table.lookup_ref(method_name);
          const java_method_typet &method_type =
            require_type::require_java_method(method_symbol.type);
          const java_method_typet::parametert &param =
            require_type::require_parameter(method_type, "x");
          require_type::require_java_generic_parameter(
            param.type(), boundedinner_name + "::NUM");

          // TODO: the bounds are not parsed yet; extend tests when fixed -
          // issue TG-1286
        }
      }
    }
  }

  WHEN("There is a generic field with a concrete type")
  {
    const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
    require_type::require_complete_java_non_generic_class(class_symbol.type);
    const struct_union_typet::componentt &belem_type =
      require_type::require_component(
        to_struct_type(class_symbol.type), "belem");
    require_type::require_pointer(
      belem_type.type(), struct_tag_typet(class_prefix + "$BoundedInner"));
    require_type::require_java_generic_type(
      belem_type.type(),
      {{require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});
  }

  WHEN("Parsing an inner class with double bounded type variable")
  {
    std::string doubleboundedinner_name = class_prefix + "$DoubleBoundedInner";
    REQUIRE(new_symbol_table.has_symbol(doubleboundedinner_name));
    THEN("The symbol type should be generic")
    {
      const symbolt &class_symbol =
        new_symbol_table.lookup_ref(doubleboundedinner_name);
      // TODO the symbol should be generic - TG-1349
      //      const java_generic_class_typet &java_generic_class_type =
      //        require_type::require_complete_java_generic_class(
      //          class_symbol.type, {doubleboundedinner_name + "::T"});

      // TODO extend when bounds are parsed correctly - TG-1286

      THEN("The fields are of correct types")
      {
        const struct_union_typet::componentt &elem =
          require_type::require_component(
            to_struct_type(class_symbol.type), "elem");
        require_type::require_java_generic_parameter(
          elem.type(), doubleboundedinner_name + "::T");

        // TODO extend when bounds are parsed correctly - TG-1286
      }
    }
  }

  GIVEN("An inner class with multiple generic parameters")
  {
    std::string twoelementinner_name = class_prefix + "$TwoElementInner";
    REQUIRE(new_symbol_table.has_symbol(twoelementinner_name));
    THEN("The symbol type should be generic with two type variables")
    {
      const symbolt &class_symbol =
        new_symbol_table.lookup_ref(twoelementinner_name);
      require_type::require_complete_java_generic_class(
        class_symbol.type,
        {twoelementinner_name + "::K", twoelementinner_name + "::V"});

      // TODO extend when bounds are parsed correctly - TG-1286

      THEN("The fields are of correct types")
      {
        const struct_union_typet::componentt &elemk =
          require_type::require_component(
            to_struct_type(class_symbol.type), "k");
        require_type::require_java_generic_parameter(
          elemk.type(), twoelementinner_name + "::K");

        const struct_union_typet::componentt &elemv =
          require_type::require_component(
            to_struct_type(class_symbol.type), "v");
        require_type::require_java_generic_parameter(
          elemv.type(), twoelementinner_name + "::V");
      }
    }
  }
}
