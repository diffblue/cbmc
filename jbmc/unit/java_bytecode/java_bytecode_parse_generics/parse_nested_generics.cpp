/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_nested_generics_fields",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "NestedGenerics", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::NestedGenerics";
  THEN("There should be a symbol for NestedGenerics with correct components")
  {
    REQUIRE(new_symbol_table.has_symbol(class_prefix));
    const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &class_type =
      require_type::require_complete_java_non_generic_class(class_symbol.type);

    THEN("The field component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN("The field2 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field2");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field3 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field3");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        const java_generic_typet generic_type_argument_1 =
          require_type::require_java_generic_type(
            type_argument_1,
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1_1 =
          generic_type_argument_1.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN("The field4 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field4");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        const java_generic_typet generic_type_argument_1 =
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

    THEN("The field5 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field5");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN("The field6 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field6");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field7 component should be a pointer to java::Generic")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field7");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field8 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field8");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});

        const typet &type_argument_2 =
          generic_field.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN("The field9 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field9");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});

        const typet &type_argument_2 =
          generic_field.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field10 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field10");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});

        const typet &type_argument_2 =
          generic_field.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field11 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field11");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }

    THEN("The field12 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field12");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        const java_generic_typet generic_type_argument_1 =
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

    THEN("The field13 component should be a pointer to java::GenericTwoParam")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(class_type, "field13");
      require_type::require_pointer(
        field_component.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Inst, "java::GenericTwoParam"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_field.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});

        const typet &type_argument_2 =
          generic_field.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }
}

SCENARIO(
  "parse_nested_generics_methods",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "NestedGenerics", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::NestedGenerics";

  THEN("Method 1 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Method 2 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method2";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of oorrect type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 3 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method3";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        const java_generic_typet &generic_type_argument_1 =
          require_type::require_java_generic_type(
            type_argument_1,
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1_1 =
          generic_type_argument_1.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Method 4 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method4";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
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
  }

  THEN("Method 5 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method5";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Method 6 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method6";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 7 should take a pointer to java::Generic")
  {
    const std::string func_name = ".method7";
    const std::string func_descriptor = ":(LGeneric;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 8 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method8";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
        const typet &type_argument_2 =
          generic_param.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Method 9 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method9";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
        const typet &type_argument_2 =
          generic_param.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 10 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method10";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
        const typet &type_argument_2 =
          generic_param.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 11 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method11";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Method 12 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method12";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
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
  }

  THEN("Method 13 should take a pointer to java::GenericTwoParam")
  {
    const std::string func_name = ".method13";
    const std::string func_descriptor = ":(LGenericTwoParam;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs have correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_param =
          require_type::require_java_generic_type(
            param_type.type(),
            {{require_type::type_argument_kindt::Inst, "java::GenericTwoParam"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_param.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
        const typet &type_argument_2 =
          generic_param.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 1 should return a java::Generic")
  {
    const std::string func_name = ".ret_method";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Ret Method 2 should return a java::Generic")
  {
    const std::string func_name = ".ret_method2";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 3 should return a java::Generic")
  {
    const std::string func_name = ".ret_method3";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        const java_generic_typet &generic_type_argument_1 =
          require_type::require_java_generic_type(
            type_argument_1,
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});
        const typet &type_argument_1_1 =
          generic_type_argument_1.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Ret Method 4 should return a java::Generic")
  {
    const std::string func_name = ".ret_method4";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
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
  }

  THEN("Ret Method 5 should return a java::Generic")
  {
    const std::string func_name = ".ret_method5";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Ret Method 6 should return a java::Generic")
  {
    const std::string func_name = ".ret_method6";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 7 should return a java::Generic")
  {
    const std::string func_name = ".ret_method7";
    const std::string func_descriptor = ":()LGeneric;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::Generic"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst,
               "java::GenericTwoParam"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 8 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method8";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
        const typet &type_argument_2 =
          generic_return.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }
  }

  THEN("Ret Method 9 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method9";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
        const typet &type_argument_2 =
          generic_return.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 10 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method10";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::Generic"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
        const typet &type_argument_2 =
          generic_return.generic_type_arguments().at(1);
        require_type::require_java_generic_type(
          type_argument_2,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 11 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method11";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }

  THEN("Ret Method 12 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method12";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst,
               "java::Generic"},
             {require_type::type_argument_kindt::Inst,
               "java::Interface_Implementation"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
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
  }

  THEN("Ret Method 13 should return a java::GenericTwoParam")
  {
    const std::string func_name = ".ret_method13";
    const std::string func_descriptor = ":()LGenericTwoParam;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type is correct")
    {
      require_type::require_pointer(
        function_call.return_type(), struct_tag_typet("java::GenericTwoParam"));

      THEN("The pointer should be generic")
      {
        const java_generic_typet &generic_return =
          require_type::require_java_generic_type(
            function_call.return_type(),
            {{require_type::type_argument_kindt::Inst, "java::GenericTwoParam"},
             {require_type::type_argument_kindt::Inst, "java::Generic"}});

        const typet &type_argument_1 =
          generic_return.generic_type_arguments().at(0);
        require_type::require_java_generic_type(
          type_argument_1,
          {{require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::java.lang.Integer"}});
      }
    }
  }
}
