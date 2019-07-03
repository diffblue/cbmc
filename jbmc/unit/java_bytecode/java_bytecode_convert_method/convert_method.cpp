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
  const class_hierarchyt class_hierarchy;
  java_bytecode_convert_methodt converter{symbol_table,
                                          null_message_handler,
                                          10,
                                          true,
                                          {},
                                          string_preprocess,
                                          class_hierarchy,
                                          false};

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
