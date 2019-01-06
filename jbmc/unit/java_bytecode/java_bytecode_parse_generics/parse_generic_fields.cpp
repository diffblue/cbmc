/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_generic_fields",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericFields", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericFields";

  WHEN("Parsing the class with generic fields")
  {
    THEN("There is a generic class symbol GenericField")
    {
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
      require_type::require_complete_java_generic_class(
        class_symbol.type, {class_prefix + "::T", class_prefix + "::S"});

      const struct_typet class_struct = to_struct_type(class_symbol.type);

      THEN("It has field f of type T")
      {
        const struct_union_typet::componentt &field =
          require_type::require_component(class_struct, "f");
        require_type::require_java_generic_parameter(
          field.type(), class_prefix + "::T");
      }

      THEN("It has field f2 pointing to Generic")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f2");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
      }

      THEN("It has field f3 pointing to Generic")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f3");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }

      THEN("It has field f4 pointing to Generic")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f4");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        THEN("The pointer should be generic")
        {
          const java_generic_typet &generic_field =
            require_type::require_java_generic_type(
              field.type(),
              {{require_type::type_argument_kindt::Inst, "java::Generic"}});

          const typet &type_argument_1 =
            generic_field.generic_type_arguments().at(0);
          require_type::require_java_generic_type(
            type_argument_1,
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
      }

      THEN("It has field f5 pointing to Generic")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f5");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::Generic"));
        THEN("The pointer should be generic")
        {
          const java_generic_typet &generic_field =
            require_type::require_java_generic_type(
              field.type(),
              {{require_type::type_argument_kindt::Inst, "java::Generic"}});

          const typet &type_argument_1 =
            generic_field.generic_type_arguments().at(0);
          const java_generic_typet &generic_type_argument_1 =
            require_type::require_java_generic_type(
              type_argument_1,
              {{require_type::type_argument_kindt::Inst, "java::Generic"}});

          const typet &type_argument_1_1 =
            generic_type_argument_1.generic_type_arguments().at(0);
          require_type::require_java_generic_type(
            type_argument_1_1,
            {{require_type::type_argument_kindt::Inst,
               "java::java.lang.Integer"}});
        }
      }

      THEN("It has field f6 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f6");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
             {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
      }

      THEN("It has field f7 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f7");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
             {require_type::type_argument_kindt::Var, class_prefix + "::S"}});
        }
      }

      THEN("It has field f8 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f8");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::java.lang.Integer"},
             {require_type::type_argument_kindt::Var,
               class_prefix + "::T"}});
        }
      }

      THEN("It has field f9 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f9");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Var,
               class_prefix + "::T"},
             {require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }

      THEN("It has field f10 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f10");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"},
             {require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }
      }

      THEN("It has field f11 pointing to GenericTwoParam")
      {
        const struct_typet::componentt &field =
          require_type::require_component(class_struct, "f11");
        require_type::require_pointer(
          field.type(), struct_tag_typet("java::GenericTwoParam"));
        THEN("The pointer should be generic")
        {
          const java_generic_typet &generic_field =
            require_type::require_java_generic_type(
              field.type(),
              {{require_type::type_argument_kindt::Inst,
                 "java::Generic"},
               {require_type::type_argument_kindt::Inst,
                 "java::GenericTwoParam"}});

          const typet &type_argument_1 =
            generic_field.generic_type_arguments().at(0);
          require_type::require_java_generic_type(
            type_argument_1,
            {{require_type::type_argument_kindt::Var,
               class_prefix + "::T"}});

          const typet &type_argument_2 =
            generic_field.generic_type_arguments().at(1);
          require_type::require_java_generic_type(
            type_argument_2,
            {{require_type::type_argument_kindt::Var,
               class_prefix + "::S"},
             {require_type::type_argument_kindt::Inst,
               "java::java.lang.Integer"}});
        }
      }
    }
  }
}
