/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_generic_class_with_generic_inner_classes_fields",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericClassWithGenericInnerClasses",
    "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericClassWithGenericInnerClasses";
  THEN(
    "There should be a symbol for "
    "GenericClassWithGenericInnerClasses with correct components")
  {
    REQUIRE(new_symbol_table.has_symbol(class_prefix));
    const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);
    const java_generic_class_typet &java_generic_class =
      require_type::require_complete_java_generic_class(
        class_symbol.type, {class_prefix + "::T"});

    THEN(
      "The field component should be a pointer to "
      "GenericClassWithGenericInnerClasses$InnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field");

      require_type::require_pointer(
        field_component.type(), struct_tag_typet(class_prefix + "$InnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }

    THEN(
      "The field2 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$GenericInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field2");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var,
             class_prefix + "::T"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN(
      "The field3 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$GenericInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field3");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }

    THEN(
      "The field4 component should be a pointer to GenericClassWithGeneric"
      "InnerClasses$GenericInnerClass$DoublyNestedInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field4");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var,
             class_prefix + "::T"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN(
      "The field5 component should be a pointer to GenericClassWithGeneric"
      "InnerClasses$GenericInnerClass$DoublyNestedInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field5");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }

    THEN(
      "The field6 component should be a pointer to GenericClassWithGeneric"
      "InnerClasses$GenericInnerClass$DoublyNestedInnerGenericClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field6");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var,
             class_prefix + "::T"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN(
      "The field7 component should be a pointer to GenericClassWithGeneric"
      "InnerClasses$GenericInnerClass$DoublyNestedInnerGenericClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field7");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }

    THEN(
      "The field8 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field8");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var,
             class_prefix + "::T"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"}});
      }
    }

    THEN(
      "The field9 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field9");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var,
             class_prefix + "::T"},
           {require_type::type_argument_kindt::Inst,
             "java::Interface_Implementation"},
           {require_type::type_argument_kindt::Var,
             class_prefix + "::T"}});
      }
    }

    THEN(
      "The field10 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
    {
      const struct_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field10");

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));

      THEN("The pointer should be generic")
      {
        require_type::require_java_generic_type(
          field_component.type(),
          {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"},
           {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
      }
    }

    THEN(
      "The field11 component should be a pointer to "
      "GenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerGenericClass")
    {
      const struct_union_typet::componentt &field_component =
        require_type::require_component(java_generic_class, "field11");

      // Declaration of field11 to be tested -
      //   GenericInnerClass<GenericClassWithGenericInnerClasses<Integer>>.
      //     DoublyNestedInnerGenericClass<T> field11;

      require_type::require_pointer(
        field_component.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));

      THEN("The pointer should be GenericClassWithGenericInnerClasses")
      {
        const java_generic_typet &generic_field =
          require_type::require_java_generic_type(
            field_component.type(),
            {{require_type::type_argument_kindt::Var,
              "java::GenericClassWithGenericInnerClasses::T"},
             {require_type::type_argument_kindt::Inst,
              "java::GenericClassWithGenericInnerClasses"},
             {require_type::type_argument_kindt::Var,
              "java::GenericClassWithGenericInnerClasses::T"}});

        THEN("Test nested Integer parameter.")
        {
          const typet &nested_generic_field =
            generic_field.generic_type_arguments().at(1);
          require_type::require_java_generic_type(
            nested_generic_field,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }
}

SCENARIO(
  "parse_generic_class_with_generic_inner_classes_methods",
  "[core][java_bytecode][java_bytecode_parse_generics][caskjd]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericClassWithGenericInnerClasses",
    "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericClassWithGenericInnerClasses";

  THEN(
    "Method 1 should take a pointer to "
    "GenericClassWithGenericInnerClasses$InnerClass")
  {
    const std::string func_name = ".method";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$InnerClass;)V";
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
        param_type.type(), struct_tag_typet(class_prefix + "$InnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 2 should take two pointers to "
    "GenericClassWithGenericInnerClasses$InnerClass")
  {
    const std::string func_name = ".method2";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$InnerClass;"
      "LGenericClassWithGenericInnerClasses$InnerClass;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 3);

    THEN("The inputs are of correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(), struct_tag_typet(class_prefix + "$InnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

      const auto &param_type2 =
        require_type::require_parameter(function_call, "input2");
      require_type::require_pointer(
        param_type2.type(), struct_tag_typet(class_prefix + "$InnerClass"));
      require_type::require_java_generic_type(
        param_type2.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 3 should take a pointer to "
    "GenericClassWithGenericInnerClasses$GenericInnerClass")
  {
    const std::string func_name = ".method3";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$GenericInnerClass;)V";
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
        param_type.type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Method 4 should take a pointer to "
    "GenericClassWithGenericInnerClasses$GenericInnerClass")
  {
    const std::string func_name = ".method4";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$GenericInnerClass;)V";
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
        param_type.type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 5 should take a pointer to GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerClass")
  {
    const std::string func_name = ".method5";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerClass;)V";
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
        param_type.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Method 6 should take a pointer to GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerClass")
  {
    const std::string func_name = ".method6";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$"
        "GenericInnerClass$DoublyNestedInnerClass;)V";
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
        param_type.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 7 should take a pointer to GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerGenericClass")
  {
    const std::string func_name = ".method7";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerGenericClass;)V";
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
        param_type.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Method 8 should take a pointer to GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerGenericClass")
  {
    const std::string func_name = ".method8";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerGenericClass;)V";
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
        param_type.type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 9 should take a pointer to "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".method9";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$TwoParamInnerClass;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of the correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Method 10 should take a pointer to "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".method10";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$TwoParamInnerClass;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs are of the correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Var,
           class_prefix + "::T"}});
    }
  }
  THEN(
    "Method 11 should take a pointer to "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".method11";
    const std::string func_descriptor =
      ":(LGenericClassWithGenericInnerClasses$TwoParamInnerClass;)V";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 2);

    THEN("The inputs should be of the correct type")
    {
      const auto &param_type =
        require_type::require_parameter(function_call, "input");
      require_type::require_pointer(
        param_type.type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        param_type.type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret Method 1 should return a "
    "GenericClassWithGenericInnerClasses$InnerClass")
  {
    const std::string func_name = ".ret_method1";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$InnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$InnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret method 2 should return a "
    "GenericClassWithGenericInnerClasses$GenericInnerClass")
  {
    const std::string func_name = ".ret_method2";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$GenericInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Ret method 3 should return a "
    "GenericClassWithGenericInnerClasses$GenericInnerClass")
  {
    const std::string func_name = ".ret_method3";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$GenericInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$GenericInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret method 4 should return a GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerClass")
  {
    const std::string func_name = ".ret_method4";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Ret method 5 should return a GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerClass")
  {
    const std::string func_name = ".ret_method5";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret method 6 should return a GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerGenericClass")
  {
    const std::string func_name = ".ret_method6";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerGenericClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Ret method 7 should return a GenericClassWithGenericInnerClasses"
    "$GenericInnerClass$DoublyNestedInnerGenericClass")
  {
    const std::string func_name = ".ret_method7";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$"
      "GenericInnerClass$DoublyNestedInnerGenericClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(
          class_prefix + "$GenericInnerClass$DoublyNestedInnerGenericClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret method 8 should return a "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".ret_method8";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$"
      "TwoParamInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"}});
    }
  }
  THEN(
    "Ret method 9 should return a "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".ret_method9";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$TwoParamInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var,
           class_prefix + "::T"},
         {require_type::type_argument_kindt::Inst,
           "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Var,
           class_prefix + "::T"}});
    }
  }
  THEN(
    "Ret method 10 should return a "
    "GenericClassWithGenericInnerClasses$TwoParamInnerClass")
  {
    const std::string func_name = ".ret_method10";
    const std::string func_descriptor =
      ":()LGenericClassWithGenericInnerClasses$TwoParamInnerClass;";
    const std::string process_func_name =
      class_prefix + func_name + func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
    const symbolt &function_symbol =
      new_symbol_table.lookup_ref(process_func_name);

    const java_method_typet &function_call =
      require_type::require_java_method(function_symbol.type, 1);

    THEN("The return type should be correct")
    {
      require_type::require_pointer(
        function_call.return_type(),
        struct_tag_typet(class_prefix + "$TwoParamInnerClass"));
      require_type::require_java_generic_type(
        function_call.return_type(),
        {{require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"},
         {require_type::type_argument_kindt::Var, class_prefix + "::T"}});
    }
  }
}
