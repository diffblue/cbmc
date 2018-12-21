/*******************************************************************\

Module: Unit tests for converting constructors and static initializers

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <memory>

#include <util/config.h>
#include <util/symbol_table.h>

#include <java_bytecode/java_bytecode_language.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

struct test_datat
{
  symbol_tablet symbol_table;
  std::string constructor_descriptor;
};

/// Verify that a given descriptor is marked as a constructor in the symbol
/// table
/// \param test_data The data to run the test on
void require_is_constructor(const test_datat &test_data)
{
  const symbolt &constructor =
    test_data.symbol_table.lookup_ref(test_data.constructor_descriptor);
  THEN("The constructor should be marked as a constructor")
  {
    java_method_typet constructor_type =
      require_type::require_java_method(constructor.type);
    REQUIRE(constructor_type.get_is_constructor());
  }
}

/// Verify that a given descriptor is not marked as a constructor in the symbol
/// table
/// \param test_data The data to run the test on
void require_is_static_initializer(const test_datat &test_data)
{
  REQUIRE(
    test_data.constructor_descriptor.find("<clinit>") != std::string::npos);
  const symbolt &constructor =
    test_data.symbol_table.lookup_ref(test_data.constructor_descriptor);
  THEN("The constructor should be marked as a constructor")
  {
    java_method_typet constructor_type =
      require_type::require_java_method(constructor.type);
    REQUIRE_FALSE(constructor_type.get_is_constructor());
  }
}

SCENARIO(
  "java_bytecode_convert_initalizers",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with some constructors")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithConstructors", "./java_bytecode/java_bytecode_convert_method");
    std::string base_constructor_name = "java::ClassWithConstructors.<init>";
    WHEN("Looking at the parameterless constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the parametered constructor")
    {
      test_datat data;
      data.constructor_descriptor =
        base_constructor_name + ":(ILjava/lang/Object;LOpaqueClass;)V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
  }
  GIVEN("A class without any constructors")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithoutConstructors",
      "./java_bytecode/java_bytecode_convert_method");
    std::string base_constructor_name = "java::ClassWithoutConstructors.<init>";
    WHEN("Looking at the default constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
  }
  GIVEN("A class with both constructors and static initalisers")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithStaticConstructor",
      "./java_bytecode/java_bytecode_convert_method");
    std::string base_class_name = "java::ClassWithStaticConstructor.";
    std::string base_constructor_name = base_class_name + "<init>";
    WHEN("Looking at the parameterless constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the parametered constructor")
    {
      test_datat data;
      data.constructor_descriptor =
        base_constructor_name + ":(ILjava/lang/Object;LOpaqueClass;)V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the static initalizer")
    {
      THEN("The static init should not be marked as a constructor")
      {
        test_datat data;
        data.constructor_descriptor = base_class_name + "<clinit>:()V";
        data.symbol_table = symbol_table;
        require_is_static_initializer(data);
      }
    }
  }
  GIVEN("A class with a static initalizer calling an opaque static initalizer")
  {
    const symbol_tablet symbol_table = load_java_class(
      "StaticClassUsingOpaqueStaticConstructor",
      "./java_bytecode/java_bytecode_convert_method");

    std::string base_class_name =
      "java::StaticClassUsingOpaqueStaticConstructor.";
    std::string base_constructor_name = base_class_name + "<init>";

    WHEN("Looking at the default constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the static initalizer")
    {
      THEN("The static init should not be marked as a constructor")
      {
        test_datat data;
        data.constructor_descriptor = base_class_name + "<clinit>:()V";
        data.symbol_table = symbol_table;
        require_is_static_initializer(data);
      }
    }
  }
  GIVEN("A class with a constructor calling opaque static initalizer")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassUsingOpaqueStaticConstructor",
      "./java_bytecode/java_bytecode_convert_method");

    std::string base_class_name = "java::ClassUsingOpaqueStaticConstructor.";
    std::string base_constructor_name = base_class_name + "<init>";

    WHEN("Looking at the parameterless constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the static initalizer for the opaque class")
    {
      THEN("The static init should not be marked as a constructor")
      {
        test_datat data;
        data.constructor_descriptor = "java::OpaqueClass.<clinit>:()V";
        data.symbol_table = symbol_table;
        require_is_static_initializer(data);
      }
    }
  }
  GIVEN("A class with a constructor calling opaque constructor")
  {
    const symbol_tablet symbol_table = load_java_class(
      "DummyClassLoadingOpaqueClass",
      "./java_bytecode/java_bytecode_convert_method");

    std::string base_class_name = "java::DummyClassLoadingOpaqueClass.";
    std::string base_constructor_name = base_class_name + "<init>";

    const symbolt &opaque_class_symbol =
      symbol_table.lookup_ref("java::OpaqueClass");
    REQUIRE(to_java_class_type(opaque_class_symbol.type).get_is_stub());

    WHEN("Looking at the parameterless constructor")
    {
      test_datat data;
      data.constructor_descriptor = base_constructor_name + ":()V";
      data.symbol_table = symbol_table;
      require_is_constructor(data);
    }
    WHEN("Looking at the static initalizer for the opaque class")
    {
      THEN("The static init should not be marked as a constructor")
      {
        test_datat data;
        data.constructor_descriptor = "java::OpaqueClass.<clinit>:()V";
        data.symbol_table = symbol_table;
        require_is_static_initializer(data);
      }
    }
    WHEN("Looking at the constructor for the opaque class")
    {
      THEN("The static init should not be marked as a constructor")
      {
        test_datat data;
        data.constructor_descriptor = "java::OpaqueClass.<init>:()V";
        data.symbol_table = symbol_table;
        require_is_constructor(data);
      }
    }
  }
}
