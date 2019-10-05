/*******************************************************************\

Module: Unit tests for converting methods.

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/expr_query.h>
#include <testing-utils/use_catch.h>

#include <util/irep.h>
#include <util/symbol_table.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

#include <java_bytecode/java_bytecode_convert_method.h>
#include <java_bytecode/java_bytecode_convert_method_class.h>
#include <java_bytecode/java_utils.h>
#include <testing-utils/message.h>

SCENARIO(
  "java_bytecode_convert_bridge_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with a bridge method")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithBridgeMethod", "./java_bytecode/java_bytecode_convert_method");

    const std::string method_name = "java::ClassWithBridgeMethod.compareTo";

    WHEN("When parsing the bridge method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref(method_name + ":(Ljava/lang/Object;)I");

      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method symbol should be of java_method_typet")
      {
        REQUIRE(function_type.get_bool(ID_C_java_method_type));
      }
      THEN("And the method should be marked as a bridge method")
      {
        REQUIRE(function_type.get_bool(ID_is_bridge_method));
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithBridgeMethod");
      }
    }
    WHEN("When parsing a non-bridge method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref(method_name + ":(LClassWithBridgeMethod;)I");

      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should not be marked as a bridge method.")
      {
        REQUIRE_FALSE(function_type.get_bool(ID_is_bridge_method));
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithBridgeMethod");
      }
    }
  }
  GIVEN("A class with a native method")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithNativeMethod", "./java_bytecode/java_bytecode_convert_method");

    const std::string method_name = "java::ClassWithNativeMethod.f";

    WHEN("When parsing the native method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref(method_name + ":()Z");

      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method symbol should be of java_method_typet")
      {
        REQUIRE(function_type.get_bool(ID_C_java_method_type));
      }
      THEN("And the method should be marked as a native method")
      {
        REQUIRE(to_java_method_type(function_type).get_native());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithNativeMethod");
      }
    }
    WHEN("When parsing a non-native method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref(method_name + ":(I)Z");

      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should not be marked as a native method.")
      {
        REQUIRE_FALSE(to_java_method_type(function_type).get_native());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithNativeMethod");
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_final_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with final and non-final methods")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithFinalMethod", "./java_bytecode/java_bytecode_convert_method");

    WHEN("When parsing a final method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::ClassWithFinalMethod.finalFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should be marked as final")
      {
        REQUIRE(function_type.get_is_final());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithFinalMethod");
      }
    }
    WHEN("When parsing a non-final method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::ClassWithFinalMethod.nonFinalFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should not be marked as final")
      {
        REQUIRE(!function_type.get_is_final());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) ==
          "java::ClassWithFinalMethod");
      }
    }
    WHEN("When parsing an opaque method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::OpaqueClass.staticFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should be marked as final")
      {
        REQUIRE(function_type.get_is_final());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(function_symbol)) == "java::OpaqueClass");
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_varargs_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with varargs and non-varargs methods")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithVarArgsMethod", "./java_bytecode/java_bytecode_convert_method");

    WHEN("When parsing a method with a variable number of arguments")
    {
      const symbolt method_symbol = symbol_table.lookup_ref(
        "java::ClassWithVarArgsMethod.varArgsFunc:([I)I");
      const java_method_typet &method_type =
        require_type::require_java_method(method_symbol.type);
      THEN("The method should be marked as varargs")
      {
        REQUIRE(method_type.get_is_varargs());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(method_symbol)) ==
          "java::ClassWithVarArgsMethod");
      }
    }
    WHEN("When parsing a method with constant number of arguments")
    {
      const symbolt method_symbol = symbol_table.lookup_ref(
        "java::ClassWithVarArgsMethod.nonVarArgsFunc:([I)I");
      const java_method_typet &method_type =
        require_type::require_java_method(method_symbol.type);
      THEN("The method should not be marked as varargs")
      {
        REQUIRE_FALSE(method_type.get_is_varargs());
      }
      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(method_symbol)) ==
          "java::ClassWithVarArgsMethod");
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_static_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with a static method.")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithStaticMethod", "./java_bytecode/java_bytecode_convert_method");

    WHEN("Parsing a static method.")
    {
      const symbolt method_symbol =
        symbol_table.lookup_ref("java::ClassWithStaticMethod.staticFunc:()I");

      THEN("The method should be marked as declared by its class")
      {
        REQUIRE(
          id2string(*declaring_class(method_symbol)) ==
          "java::ClassWithStaticMethod");
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_synthetic_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with a synthetic method.")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithSyntheticMethod",
      "./java_bytecode/java_bytecode_convert_method");

    WHEN("Parsing a synthetic method.")
    {
      const java_method_typet *const synthetic_method =
        type_try_dynamic_cast<java_method_typet>(symbol_table.lookup_ref(
          "java::ClassWithSyntheticMethod.access$000:()I").type);
      REQUIRE(synthetic_method);

      THEN("The method should be marked as synthetic.")
      {
        REQUIRE(synthetic_method->is_synthetic());
      }
    }
    WHEN("Parsing a non synthetic method.")
    {
      const java_method_typet *const non_synthetic_method =
        type_try_dynamic_cast<java_method_typet>(symbol_table.lookup_ref(
          "java::ClassWithSyntheticMethod.inaccessible:()I").type);
      REQUIRE(non_synthetic_method);

      THEN("The method should not be marked as synthetic.")
      {
        REQUIRE(!non_synthetic_method->is_synthetic());
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_method_with_getstatic",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class that reads a static field.")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassReadingStaticField",
      "./java_bytecode/java_bytecode_convert_method");

    WHEN("Converting the method that reads said field")
    {
      const auto &method_symbol =
        symbol_table.lookup_ref("java::ClassReadingStaticField.test:()I");

      THEN(
        "There should be a symbol expression attributed to bytecode index "
        "0 (the getstatic instruction)")
      {
        bool found = false;
        method_symbol.value.visit_pre([&found](const exprt &subexpr) {
          if(
            const auto symbol_expr =
              expr_try_dynamic_cast<symbol_exprt>(subexpr))
          {
            if(
              symbol_expr->source_location().get_java_bytecode_index() == "0" &&
              symbol_expr->get_identifier() ==
                "java::ClassReadingStaticField.x")
              found = true;
          }
        });

        REQUIRE(found);
      }
    }
  }
}

/// Allow access to private methods so that they can be unit tested
class java_bytecode_convert_method_unit_testt
{
public:
  static exprt
  convert_aload(const irep_idt &statement, const exprt::operandst &op)
  {
    return java_bytecode_convert_methodt::convert_aload(statement, op);
  }

  static code_blockt convert_astore(
    java_bytecode_convert_methodt &converter,
    const irep_idt &statement,
    const exprt::operandst &op,
    const source_locationt &location)
  {
    return converter.convert_astore(statement, op, location);
  }

  static exprt variable(
    java_bytecode_convert_methodt &converter,
    const exprt &arg,
    char type_char,
    size_t address)
  {
    return converter.variable(arg, type_char, address);
  }

  static void add_variable(
    java_bytecode_convert_methodt &converter,
    std::size_t index,
    symbol_exprt symbol_expr,
    std::size_t start_pc,
    std::size_t length,
    bool is_parameter,
    std::vector<java_bytecode_convert_methodt::holet> holes)
  {
    converter.variables[index].emplace_back(
      std::move(symbol_expr), start_pc, length, is_parameter, std::move(holes));
  }

  static exprt convert_load(
    java_bytecode_convert_methodt &converter,
    const exprt &index,
    char type_char,
    size_t address)
  {
    return converter.convert_load(index, type_char, address);
  }

  static code_blockt convert_store(
    java_bytecode_convert_methodt &converter,
    const irep_idt &statement,
    const exprt &arg0,
    const exprt::operandst &op,
    const java_bytecode_convert_methodt::method_offsett address,
    const source_locationt &location)
  {
    return converter.convert_store(statement, arg0, op, address, location);
  }
};

SCENARIO(
  "baload byte array",
  "[core][java_bytecode][java_bytecode_convert_method][convert_aload]")
{
  GIVEN("A byte array")
  {
    const typet byte_array_type = java_array_type('b');
    const symbol_exprt byte_array{"byte_array", byte_array_type};
    const exprt offset = from_integer(1, java_int_type());
    WHEN("baload is called on the byte array")
    {
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_aload(
          "baload", {byte_array, offset});
      THEN("The Result is of the form `(int)(*(byte_array->data + offset))`")
      // See \ref java_bytecode_promotion on why we need a typecast to int.
      {
        const auto query = make_query(result)
                             .as<typecast_exprt>()[0]
                             .as<dereference_exprt>()[0]
                             .as<plus_exprt>();
        REQUIRE(query[1].get() == offset);
        auto member = query[0].as<member_exprt>();
        REQUIRE(member.get().get_component_name() == "data");
        REQUIRE(member[0].as<dereference_exprt>()[0].get() == byte_array);
        REQUIRE(result.type() == java_int_type());
        // byte_array->data has type *byte
        REQUIRE(member.get().type() == pointer_type(java_byte_type()));
      }
    }
  }
}

SCENARIO(
  "baload boolean array",
  "[core][java_bytecode][java_bytecode_convert_method][convert_aload]")
{
  GIVEN("A boolean array")
  {
    const typet boolean_array_type = java_array_type('z');
    const symbol_exprt boolean_array{"boolean_array", boolean_array_type};
    const exprt offset = from_integer(2, java_int_type());
    WHEN("baload is called on the byte array")
    {
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_aload(
          "baload", {boolean_array, offset});
      THEN("The result is of the form `(int)(*(boolean_array->data + offset))`")
      // See \ref java_bytecode_promotion on why we need a typecast to int.
      {
        const auto query = make_query(result)
                             .as<typecast_exprt>()[0]
                             .as<dereference_exprt>()[0]
                             .as<plus_exprt>();
        REQUIRE(query[1].get() == offset);
        REQUIRE(
          query[0].as<member_exprt>()[0].as<dereference_exprt>()[0].get() ==
          boolean_array);
        // boolean_array->data has type *boolean
        REQUIRE(
          query[0].as<member_exprt>().get().type() ==
          pointer_type(java_boolean_type()));
      }
    }
  }
}

SCENARIO(
  "iaload int array",
  "[core][java_bytecode][java_bytecode_convert_method][convert_aload]")
{
  GIVEN("An int array")
  {
    const typet int_array_type = java_array_type('i');
    const symbol_exprt int_array{"int_array", int_array_type};
    const exprt offset = from_integer(2, java_int_type());
    WHEN("iaload is called on the int array")
    {
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_aload(
          "iaload", {int_array, offset});
      THEN("The result is of the form `*(int_array->data + offset)`")
      {
        const auto query =
          make_query(result).as<dereference_exprt>()[0].as<plus_exprt>();
        REQUIRE(query[1].get() == offset);
        REQUIRE(
          query[0].as<member_exprt>()[0].as<dereference_exprt>()[0].get() ==
          int_array);
        // int_array->data has type *int
        REQUIRE(
          query[0].as<member_exprt>().get().type() ==
          pointer_type(java_int_type()));
      }
    }
  }
}

SCENARIO(
  "astore",
  "[core][java_bytecode][java_bytecode_convert_method][convert_astore]")
{
  symbol_tablet symbol_table;
  java_string_library_preprocesst string_preprocess;
  const class_hierarchyt class_hierarchy{};
  const bool assert_no_exceptions_thrown = false;
  java_bytecode_convert_methodt converter{symbol_table,
                                          null_message_handler,
                                          10,
                                          true,
                                          {},
                                          string_preprocess,
                                          class_hierarchy,
                                          false,
                                          assert_no_exceptions_thrown};

  GIVEN("An int array")
  {
    const source_locationt location;
    const typet int_array_type = java_array_type('i');
    const symbol_exprt int_array{"int_array", int_array_type};
    const exprt offset = from_integer(3, java_int_type());
    const exprt value = from_integer(4, java_int_type());
    WHEN("iastore is called on the int array")
    {
      const code_blockt result =
        java_bytecode_convert_method_unit_testt::convert_astore(
          converter, "iastore", {int_array, offset, value}, location);
      THEN(
        "The result contains 1 statement of the form `*(int_array->data + 3) = "
        "4`")
      {
        REQUIRE(result.statements().size() == 1);
        auto query = make_query(result.statements()[0]).as<code_assignt>();
        REQUIRE(query[1].get() == value);
        auto plus = query[0].as<dereference_exprt>()[0].as<plus_exprt>();
        REQUIRE(plus[1].get() == offset);
        REQUIRE(
          plus[0].as<member_exprt>().get().get_component_name() == "data");
        REQUIRE(
          plus[0].as<member_exprt>()[0].as<dereference_exprt>()[0].get() ==
          int_array);
        THEN("int_array->data has type *int")
        {
          REQUIRE(
            plus[0].as<member_exprt>().get().type() ==
            pointer_type(java_int_type()));
        }
      }
    }
  }

  GIVEN("A boolean array")
  {
    const source_locationt location;
    const typet boolean_array_type = java_array_type('z');
    const symbol_exprt boolean_array{"boolean_array", boolean_array_type};
    const exprt offset = from_integer(3, java_int_type());
    const exprt value = from_integer(true, java_boolean_type());
    WHEN("bastore is called on the boolean array")
    {
      const code_blockt result =
        java_bytecode_convert_method_unit_testt::convert_astore(
          converter, "bastore", {boolean_array, offset, value}, location);
      THEN(
        "The result contains 1 statement of the form "
        "`*(boolean_array->data + 3) = true`")
      {
        REQUIRE(result.statements().size() == 1);
        auto query = make_query(result.statements()[0]).as<code_assignt>();
        REQUIRE(query[1].get() == value);
        auto plus = query[0].as<dereference_exprt>()[0].as<plus_exprt>();
        REQUIRE(plus[1].get() == offset);
        REQUIRE(
          plus[0].as<member_exprt>().get().get_component_name() == "data");
        REQUIRE(
          plus[0].as<member_exprt>()[0].as<dereference_exprt>()[0].get() ==
          boolean_array);
        THEN("boolean_array->data has type *boolean")
        {
          REQUIRE(
            plus[0].as<member_exprt>().get().type() ==
            pointer_type(java_boolean_type()));
        }
      }
    }
    WHEN("iastore is called on the boolean array")
    {
      const code_blockt result =
        java_bytecode_convert_method_unit_testt::convert_astore(
          converter, "iastore", {boolean_array, offset, value}, location);
      THEN(
        "The result contains 1 statement of the form "
        "`*(((int[])boolean_array)->data + offset)`")
      {
        REQUIRE(result.statements().size() == 1);
        REQUIRE(
          make_query(result.statements()[0])
            .as<code_assignt>()[0]
            .as<dereference_exprt>()[0]
            .as<plus_exprt>()[0]
            .as<member_exprt>()[0]
            .as<dereference_exprt>()[0]
            .as<typecast_exprt>()
            .get()
            .type() == java_array_type('i'));
      }
    }
  }
}

SCENARIO(
  "java convert method variable",
  "[core][java_bytecode][java_bytecode_convert_method][variable]")
{
  symbol_tablet symbol_table;
  java_string_library_preprocesst string_preprocess;
  const class_hierarchyt class_hierarchy{};
  const std::size_t max_array_length = 10;
  const bool throw_assertion_error = true;
  const bool threading_support = false;
  const bool assert_no_exceptions_thrown = false;
  java_bytecode_convert_methodt converter{symbol_table,
                                          null_message_handler,
                                          max_array_length,
                                          throw_assertion_error,
                                          {},
                                          string_preprocess,
                                          class_hierarchy,
                                          threading_support,
                                          assert_no_exceptions_thrown};

  GIVEN("An int_array variable")
  {
    const source_locationt location;
    const typet int_array_type = java_array_type('i');
    const symbol_exprt int_array{"int_array", int_array_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, int_array, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is retrieved via its index with type_char a")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result = java_bytecode_convert_method_unit_testt::variable(
        converter, index_expr, 'a', address);
      THEN("the result is int_array")
      {
        REQUIRE(result == int_array);
      }
    }
    WHEN("There is no variable at the given index")
    {
      const constant_exprt index_expr =
        from_integer(variable_index + 1, java_int_type());
      const exprt result = java_bytecode_convert_method_unit_testt::variable(
        converter, index_expr, 'a', address);
      THEN("A new reference variable is created")
      {
        REQUIRE(result != int_array);
        REQUIRE(can_cast_expr<symbol_exprt>(result));
        REQUIRE(result.type() == java_type_from_char('a'));
      }
    }
  }
  GIVEN("An Object variable")
  {
    const source_locationt location;
    const typet object_type = java_lang_object_type();
    const symbol_exprt obj{"obj", object_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, obj, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is retrieved via its index with type_char a")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result = java_bytecode_convert_method_unit_testt::variable(
        converter, index_expr, 'a', address);
      THEN("the result is obj")
      {
        REQUIRE(result == obj);
      }
    }
  }
  GIVEN("An long variable")
  {
    const source_locationt location;
    const typet long_type = java_long_type();
    const symbol_exprt long_var{"long_var", long_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, long_var, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is retrieved via its index with type_char l")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result = java_bytecode_convert_method_unit_testt::variable(
        converter, index_expr, 'l', address);
      THEN("the result is long_var")
      {
        REQUIRE(result == long_var);
      }
    }
  }
}

SCENARIO(
  "java convert load",
  "[core][java_bytecode][java_bytecode_convert_method][convert_load]")
{
  symbol_tablet symbol_table;
  java_string_library_preprocesst string_preprocess;
  const class_hierarchyt class_hierarchy{};
  const std::size_t max_array_length = 10;
  const bool throw_assertion_error = true;
  const bool threading_support = false;
  const bool assert_no_exceptions_thrown = false;
  java_bytecode_convert_methodt converter{symbol_table,
                                          null_message_handler,
                                          max_array_length,
                                          throw_assertion_error,
                                          {},
                                          string_preprocess,
                                          class_hierarchy,
                                          threading_support,
                                          assert_no_exceptions_thrown};

  GIVEN("An int_array variable")
  {
    const source_locationt location;
    const typet int_array_type = java_array_type('i');
    const symbol_exprt int_array{"int_array", int_array_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, int_array, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is loaded with aload")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_load(
          converter, index_expr, 'a', address);
      THEN("the result is int_array")
      {
        REQUIRE(result == int_array);
      }
    }
    WHEN("There is no variable at the given index")
    {
      const constant_exprt index_expr =
        from_integer(variable_index + 1, java_int_type());
      const exprt result = java_bytecode_convert_method_unit_testt::variable(
        converter, index_expr, 'a', address);
      THEN("A new reference variable is created")
      {
        REQUIRE(result != int_array);
        REQUIRE(can_cast_expr<symbol_exprt>(result));
        REQUIRE(result.type() == java_type_from_char('a'));
      }
    }
  }
  GIVEN("An Object variable")
  {
    const source_locationt location;
    const typet object_type = java_lang_object_type();
    const symbol_exprt obj{"obj", object_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, obj, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is loaded with aload")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_load(
          converter, index_expr, 'a', address);
      THEN("the result is obj")
      {
        REQUIRE(result == obj);
      }
    }
  }
  GIVEN("A long variable")
  {
    const source_locationt location;
    const typet long_type = java_long_type();
    const symbol_exprt long_var{"long_var", long_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter, variable_index, long_var, start_pc, length, is_parameter, {});
    const std::size_t address = 0;
    WHEN("The variable is loaded with lload")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_load(
          converter, index_expr, 'l', address);
      THEN("the result is long_var")
      {
        REQUIRE(result == long_var);
      }
    }
  }
  GIVEN("A boolean variable")
  {
    const source_locationt location;
    const symbol_exprt boolean_var{"boolean_var", java_boolean_type()};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter,
      variable_index,
      boolean_var,
      start_pc,
      length,
      is_parameter,
      {});
    const std::size_t address = 0;
    WHEN("The variable is loaded with iload")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const exprt result =
        java_bytecode_convert_method_unit_testt::convert_load(
          converter, index_expr, 'i', address);
      THEN("the result is (int)boolean_var")
      {
        REQUIRE(result.type() == java_int_type());
        REQUIRE(
          make_query(result).as<typecast_exprt>()[0].get() == boolean_var);
      }
    }
  }
}

SCENARIO(
  "convert store",
  "[core][java_bytecode][java_bytecode_convert_method][convert_store]")
{
  symbol_tablet symbol_table;
  java_string_library_preprocesst string_preprocess;
  const class_hierarchyt class_hierarchy{};
  const std::size_t max_array_length = 10;
  const bool throw_assertion_error = true;
  const bool threading_support = false;
  const bool assert_no_exceptions_thrown = false;
  java_bytecode_convert_methodt converter{symbol_table,
                                          null_message_handler,
                                          max_array_length,
                                          throw_assertion_error,
                                          {},
                                          string_preprocess,
                                          class_hierarchy,
                                          threading_support,
                                          assert_no_exceptions_thrown};

  GIVEN("An int_array variable")
  {
    const source_locationt location;
    const typet int_array_type = java_array_type('i');
    const symbol_exprt int_array{"int_array", int_array_type};
    const symbol_exprt int_array_copy{"int_array_copy", int_array_type};
    const std::size_t variable_index = 0;
    const std::size_t start_pc = 0;
    const std::size_t length = 1;
    const bool is_parameter = false;
    java_bytecode_convert_method_unit_testt::add_variable(
      converter,
      variable_index,
      int_array_copy,
      start_pc,
      length,
      is_parameter,
      {});
    WHEN("astore is called on the int array")
    {
      const constant_exprt index_expr =
        from_integer(variable_index, java_int_type());
      const code_blockt result_code =
        java_bytecode_convert_method_unit_testt::convert_store(
          converter, "astore", index_expr, {int_array}, 0, location);

      THEN(
        "The result is one assignment of the form "
        "`int_array_copy = int_array`")
      {
        REQUIRE(result_code.statements().size() == 1);
        auto assign_query =
          make_query(result_code.statements()[0]).as<code_assignt>();
        REQUIRE(can_cast_expr<symbol_exprt>(assign_query[0].get()));
        REQUIRE(assign_query[1].get() == int_array);
        THEN("Left-hand-side has type int array")
        {
          REQUIRE(assign_query[0].get().type() == int_array_type);
        }
      }
    }
  }
}

TEST_CASE(
  "create_parameter_names",
  "[core][java_bytecode][java_bytecode_convert_method]"
  "[create_parameter_names]")
{
  // Arrange
  java_bytecode_parse_treet::methodt m;
  irep_idt method_identifier = "someClass.someMethod";

  // The parameters should be already populated, but not have names, ids
  code_typet::parametert this_param;
  this_param.set_this();
  this_param.type() = java_lang_object_type();
  code_typet::parametert ref_to_inner;
  ref_to_inner.type() = java_lang_object_type();
  code_typet::parametert other_param;
  other_param.type() = java_lang_object_type();
  java_method_typet::parameterst parameters{
    this_param, ref_to_inner, other_param};
  for(const auto param : parameters)
  {
    REQUIRE(param.get_identifier().empty());
    REQUIRE(param.get_base_name().empty());
  }

  // The method should have local variables with names
  // We allocate three slots for three variables with size 1
  java_bytecode_convert_methodt::method_offsett slots_for_parameters = 3;
  java_bytecode_parse_treet::methodt::local_variablet this_local_var;
  this_local_var.name = "this";
  this_local_var.length = 1;
  this_local_var.index = 0;
  java_bytecode_parse_treet::methodt::local_variablet ref_to_inner_local_var;
  ref_to_inner_local_var.name = "this$0";
  ref_to_inner_local_var.length = 1;
  ref_to_inner_local_var.index = 1;
  java_bytecode_parse_treet::methodt::local_variablet other_local_var;
  other_local_var.name = "other";
  other_local_var.length = 1;
  other_local_var.index = 2;
  m.local_variable_table = {
    this_local_var, ref_to_inner_local_var, other_local_var};
  REQUIRE(parameters.size() == 3);

  // Act
  create_parameter_names(
    m, method_identifier, parameters, slots_for_parameters);

  // Assert side effects
  REQUIRE(parameters.size() == 3);
  REQUIRE(parameters.at(0).get_identifier() == "someClass.someMethod::this");
  REQUIRE(parameters.at(1).get_identifier() == "someClass.someMethod::this$0");
  REQUIRE(parameters.at(2).get_identifier() == "someClass.someMethod::other");
  REQUIRE(parameters.at(0).get_base_name() == "this");
  REQUIRE(parameters.at(1).get_base_name() == "this$0");
  REQUIRE(parameters.at(2).get_base_name() == "other");
}

TEST_CASE(
  "create_parameter_symbols",
  "[core][java_bytecode][java_bytecode_convert_method]"
  "[create_parameter_symbols]")
{
  // Arrange
  const irep_idt method_id = "someClass.someMethod";
  // The parameters should be already populated, with names, ids
  code_typet::parametert this_param;
  this_param.set_this();
  this_param.type() = java_lang_object_type();
  this_param.set_identifier(id2string(method_id) + "::this");
  this_param.set_base_name("this");
  code_typet::parametert ref_to_inner;
  ref_to_inner.type() = java_lang_object_type();
  ref_to_inner.set_identifier(id2string(method_id) + "::this$0");
  ref_to_inner.set_base_name("this$0");
  code_typet::parametert other_param;
  other_param.type() = java_lang_object_type();
  other_param.set_identifier(id2string(method_id) + "::other");
  other_param.set_base_name("other");
  java_method_typet::parameterst parameters{
    this_param, ref_to_inner, other_param};

  variablest variables;

  symbol_tablet symbol_table;
  REQUIRE(symbol_table.symbols.empty());

  // Act
  create_parameter_symbols(parameters, variables, symbol_table);

  // Assert side effects on symbol table
  REQUIRE(symbol_table.symbols.size() == 3);
  const symbolt this_symbol =
    symbol_table.lookup_ref(id2string(method_id) + "::this");
  REQUIRE(this_symbol.name == id2string(method_id) + "::this");
  REQUIRE(this_symbol.base_name == "this");
  REQUIRE(this_symbol.type == java_lang_object_type());
  REQUIRE(this_symbol.mode == ID_java);
  const symbolt inner_symbol =
    symbol_table.lookup_ref(id2string(method_id) + "::this$0");
  REQUIRE(inner_symbol.name == id2string(method_id) + "::this$0");
  REQUIRE(inner_symbol.base_name == "this$0");
  REQUIRE(inner_symbol.type == java_lang_object_type());
  REQUIRE(inner_symbol.mode == ID_java);
  const symbolt other_symbol =
    symbol_table.lookup_ref(id2string(method_id) + "::other");
  REQUIRE(other_symbol.name == id2string(method_id) + "::other");
  REQUIRE(other_symbol.base_name == "other");
  REQUIRE(other_symbol.type == java_lang_object_type());
  REQUIRE(other_symbol.mode == ID_java);

  // Assert side effects on variables
  REQUIRE(variables.size() == 3);
  REQUIRE(
    variables[0][0].symbol_expr.get_identifier() ==
    id2string(method_id) + "::this");
  REQUIRE(
    variables[1][0].symbol_expr.get_identifier() ==
    id2string(method_id) + "::this$0");
  REQUIRE(
    variables[2][0].symbol_expr.get_identifier() ==
    id2string(method_id) + "::other");
}
