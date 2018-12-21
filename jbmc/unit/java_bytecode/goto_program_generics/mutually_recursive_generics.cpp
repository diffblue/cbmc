/*******************************************************************\

Module: Unit tests for parsing mutually generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_goto_statements.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/catch.hpp>

SCENARIO(
  "Generics class with mutually recursive_generic parameters",
  "[core][java_bytecode][goto_programs_generics]")
{
  const symbol_tablet &symbol_table = load_java_class(
    "MutuallyRecursiveGenerics",
    "./java_bytecode/goto_program_generics",
    "MutuallyRecursiveGenerics.f");

  const std::string class_prefix = "java::MutuallyRecursiveGenerics";

  REQUIRE(symbol_table.has_symbol(class_prefix));

  WHEN(
    "parsing class which has generic type parameters and two field with those"
    "parameters in use")
  {
    const auto &root = symbol_table.lookup_ref(class_prefix);
    const typet &type = root.type;
    REQUIRE(type.id() == ID_struct);

    // needs an `example1` local variable ...
    const struct_union_typet::componentt &example1 =
      require_type::require_component(to_struct_type(type), "example1");

    // ... which is generic and has two explicit generic parameter
    // instantiations, String and Integer ...
    const java_generic_typet &gen_type =
      require_type::require_java_generic_type(
        example1.type(),
        {{require_type::type_argument_kindt::Inst, "java::java.lang.String"},
         {require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});

    // ... which is of type `KeyValue` ...
    const auto &subtype = gen_type.subtype();
    const auto &key_value =
      symbol_table.lookup_ref(to_struct_tag_type(subtype).get_identifier());
    REQUIRE(key_value.type.id() == ID_struct);
    REQUIRE(key_value.name == "java::KeyValue");

    // ... and contains two local variables of type `KeyValue` ...
    const auto &next =
      require_type::require_component(to_struct_type(key_value.type), "next");
    const auto &reverse = require_type::require_component(
      to_struct_type(key_value.type), "reverse");

    // ... where `next` has the same generic parameter instantiations ...
    const java_generic_typet &next_type =
      require_type::require_java_generic_type(
        next.type(),
        {{require_type::type_argument_kindt::Var, "java::KeyValue::K"},
         {require_type::type_argument_kindt::Var, "java::KeyValue::V"}});
    REQUIRE(next_type.subtype().id() == ID_struct_tag);
    const struct_tag_typet &next_symbol =
      to_struct_tag_type(next_type.subtype());
    REQUIRE(
      symbol_table.lookup_ref(next_symbol.get_identifier()).name ==
      "java::KeyValue");

    // ... and `reverse` has the same but in reversed order
    const java_generic_typet &reverse_type =
      require_type::require_java_generic_type(
        reverse.type(),
        {{require_type::type_argument_kindt::Var, "java::KeyValue::V"},
         {require_type::type_argument_kindt::Var, "java::KeyValue::K"}});
    REQUIRE(next_type.subtype().id() == ID_struct_tag);
    const struct_tag_typet &reverse_symbol =
      to_struct_tag_type(reverse_type.subtype());
    REQUIRE(
      symbol_table.lookup_ref(next_symbol.get_identifier()).name ==
      "java::KeyValue");
  }
  WHEN("The class of type `MutuallyRecursiveGenerics` is created")
  {
    const std::vector<codet> &entry_point_code =
      require_goto_statements::require_entry_point_statements(symbol_table);

    const auto has_key_and_value_field = [&](
      const irep_idt &field,
      const irep_idt &key_type,
      const irep_idt &val_type) {
      require_goto_statements::require_struct_component_assignment(
        field, {}, "key", key_type, {}, entry_point_code, symbol_table);
      require_goto_statements::require_struct_component_assignment(
        field, {}, "value", val_type, {}, entry_point_code, symbol_table);
    };

    const irep_idt &tmp_object_name =
      require_goto_statements::require_entry_point_argument_assignment(
        "this", entry_point_code);

    THEN(
      "The Object has a field `example1` of type `KeyValue<String, Integer>`")
    {
      const auto &example1_field =
        require_goto_statements::require_struct_component_assignment(
          tmp_object_name,
          {},
          "example1",
          "java::KeyValue",
          {},
          entry_point_code,
          symbol_table);

      THEN(
        "Object 'example1' has field 'key' of type `String` and field `value` "
        "of type `Integer`")
      {
        has_key_and_value_field(
          example1_field, "java::java.lang.String", "java::java.lang.Integer");
      }

      THEN("`example1` has field next")
      {
        const auto &next_field =
          require_goto_statements::require_struct_component_assignment(
            example1_field,
            {},
            "next",
            "java::KeyValue",
            {},
            entry_point_code,
            symbol_table);
        has_key_and_value_field(
          next_field, "java::java.lang.String", "java::java.lang.Integer");
      }
      THEN("`example1` has field `reverse`")
      {
        const auto &reverse_field =
          require_goto_statements::require_struct_component_assignment(
            example1_field,
            {},
            "reverse",
            "java::KeyValue",
            {},
            entry_point_code,
            symbol_table);
        has_key_and_value_field(
          reverse_field, "java::java.lang.Integer", "java::java.lang.String");
      }
    }
    THEN(
      "The Object has a field `example2` of type `Three<Byte, Character, "
      "Integer>`")
    {
      const auto &example2_field =
        require_goto_statements::require_struct_component_assignment(
          tmp_object_name,
          {},
          "example2",
          "java::Three",
          {},
          entry_point_code,
          symbol_table);

      const auto has_x_e_u_fields = [&](
        const irep_idt &field,
        const irep_idt &x_type,
        const irep_idt &e_type,
        const irep_idt &u_type) {
        require_goto_statements::require_struct_component_assignment(
          field, {}, "x", x_type, {}, entry_point_code, symbol_table);
        require_goto_statements::require_struct_component_assignment(
          field, {}, "e", e_type, {}, entry_point_code, symbol_table);
        require_goto_statements::require_struct_component_assignment(
          field, {}, "u", u_type, {}, entry_point_code, symbol_table);
      };

      THEN(
        "Object 'example2' has field 'x' of type `Byte`, field `u` of type "
        "`Character` and a field `e` of type `Integer`.")
      {
        has_x_e_u_fields(
          example2_field,
          "java::java.lang.Byte",
          "java::java.lang.Character",
          "java::java.lang.Integer");

        THEN("`example2` has field `rotate`")
        {
          const auto &rotate_field =
            require_goto_statements::require_struct_component_assignment(
              example2_field,
              {},
              "rotate",
              "java::Three",
              {},
              entry_point_code,
              symbol_table);
          has_x_e_u_fields(
            rotate_field,
            "java::java.lang.Integer",
            "java::java.lang.Byte",
            "java::java.lang.Character");

          THEN("`rotate` has itself a field `rotate` ... ")
          {
            const auto &rotate_rec_field =
              require_goto_statements::require_struct_component_assignment(
                rotate_field,
                {},
                "rotate",
                "java::Three",
                {},
                entry_point_code,
                symbol_table);
            has_x_e_u_fields(
              rotate_rec_field,
              "java::java.lang.Character",
              "java::java.lang.Integer",
              "java::java.lang.Byte");
          }
          THEN("`rotate` has also a field `normal` ... ")
          {
            const auto &rotate_normal_field =
              require_goto_statements::require_struct_component_assignment(
                rotate_field,
                {},
                "normal",
                "java::Three",
                {},
                entry_point_code,
                symbol_table);
            has_x_e_u_fields(
              rotate_normal_field,
              "java::java.lang.Integer",
              "java::java.lang.Byte",
              "java::java.lang.Character");
          }
        }
        THEN("`example2` has field `normal`")
        {
          const auto &normal_field =
            require_goto_statements::require_struct_component_assignment(
              example2_field,
              {},
              "normal",
              "java::Three",
              {},
              entry_point_code,
              symbol_table);
          has_x_e_u_fields(
            normal_field,
            "java::java.lang.Byte",
            "java::java.lang.Character",
            "java::java.lang.Integer");
          THEN("`normal` has itself a field `normal`")
          {
            const auto &normal_rec_field =
              require_goto_statements::require_struct_component_assignment(
                example2_field,
                {},
                "normal",
                "java::Three",
                {},
                entry_point_code,
                symbol_table);
            has_x_e_u_fields(
              normal_rec_field,
              "java::java.lang.Byte",
              "java::java.lang.Character",
              "java::java.lang.Integer");
          }
          THEN("`normal` has also a field `rotate`")
          {
            const auto &normal_rotate_field =
              require_goto_statements::require_struct_component_assignment(
                example2_field,
                {},
                "rotate",
                "java::Three",
                {},
                entry_point_code,
                symbol_table);
            has_x_e_u_fields(
              normal_rotate_field,
              "java::java.lang.Integer",
              "java::java.lang.Byte",
              "java::java.lang.Character");
          }
        }
      }
    }
  }

  // TODO: add test for TG-3828
}
