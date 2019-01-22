/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Limited

\*******************************************************************/

#include <java_bytecode/load_method_by_regex.h>
#include <testing-utils/require_vectors_equal_unordered.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "load_method_by_regex::does_pattern_miss_descriptor",
  "[core][java_bytecode][load_method_by_regex]")
{
  GIVEN("A string with a java prefix and no descriptor")
  {
    const std::string pattern = "java::com.diffblue.ClassName.methodName";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should miss discriptor")
      {
        REQUIRE(result);
      }
    }
  }
  GIVEN("A string with a java prefix and a descriptor")
  {
    const std::string pattern = "java::com.diffblue.ClassName.methodName:()V";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should have the discriptor")
      {
        REQUIRE_FALSE(result);
      }
    }
  }
  GIVEN("A string without a java prefix and without a descriptor")
  {
    const std::string pattern = "com.diffblue.ClassName.methodName";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should miss discriptor")
      {
        REQUIRE(result);
      }
    }
  }
  GIVEN("A string without a java prefix and with a descriptor")
  {
    const std::string pattern = "com.diffblue.ClassName.methodName:()V";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should have the discriptor")
      {
        REQUIRE_FALSE(result);
      }
    }
  }
  GIVEN("A string with an almost java prefix and no descriptor")
  {
    const std::string pattern = "java:com.diffblue.ClassName.methodName";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should classify the last : as a descriptor")
      {
        REQUIRE_FALSE(result);
      }
    }
  }
  GIVEN("A string with an almost java prefix and with a descriptor")
  {
    const std::string pattern = "java:com.diffblue.ClassName.methodName:()V";
    WHEN("When calling does_pattern_miss_descriptor")
    {
      const bool result = does_pattern_miss_descriptor(pattern);
      THEN("It should have the discriptor")
      {
        REQUIRE_FALSE(result);
      }
    }
  }
}

static symbolt create_method_symbol(const std::string &method_name)
{
  symbolt new_symbol;
  new_symbol.name = method_name;
  new_symbol.type = java_method_typet{{}, nil_typet{}};
  return new_symbol;
}

static void require_result_for_pattern(
  const std::string &pattern,
  const std::vector<irep_idt> &expected,
  const symbol_tablet &symbol_table)
{
  WHEN("Constructing a load_method_by_regex")
  {
    const auto matcher = build_load_method_by_regex(pattern);
    const auto &results = matcher(symbol_table);
    if(expected.size() == 1)
    {
      THEN("Expect " + id2string(expected[0]))
      {
        require_vectors_equal_unordered(results, expected);
      }
    }
    else
    {
      THEN("Expect " + std::to_string(expected.size()) + " symbols")
      {
        require_vectors_equal_unordered(results, expected);
      }
    }
  }
}

SCENARIO("load_method_by_regex", "[core][java_bytecode][load_method_by_regex]")
{
  symbol_tablet symbol_table;
  symbol_table.add(create_method_symbol("java::pack.Class.methodName:()V"));
  symbol_table.add(create_method_symbol("java::pack.Class.anotherMethod:()V"));
  symbol_table.add(create_method_symbol("java::pack.Different.methodName:()V"));
  symbol_table.add(create_method_symbol("java::another.Class.methodName:()V"));

  GIVEN("A pattern without java prefix, without descriptor, no regex")
  {
    const std::string pattern = "pack.Class.methodName";
    const std::vector<irep_idt> expected = {"java::pack.Class.methodName:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern with java prefix, without descriptor, no regex")
  {
    const std::string pattern = "java::pack.Class.methodName";
    const std::vector<irep_idt> expected = {"java::pack.Class.methodName:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern with java prefix, with descriptor, no regex")
  {
    const std::string pattern = R"(java::pack.Class.methodName:\(\)V)";
    const std::vector<irep_idt> expected = {"java::pack.Class.methodName:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern with java prefix, with wrong descriptor, no regex")
  {
    const std::string pattern = R"(java::pack.Class.methodName:\(I\)V)";
    const std::vector<irep_idt> expected = {};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern with java prefix, without descriptor, with regex")
  {
    const std::string pattern = "java::pack.Class..*";
    const std::vector<irep_idt> expected = {
      "java::pack.Class.methodName:()V", "java::pack.Class.anotherMethod:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern without java prefix, without descriptor, with regex")
  {
    const std::string pattern = "pack.Class..*";
    const std::vector<irep_idt> expected = {
      "java::pack.Class.methodName:()V", "java::pack.Class.anotherMethod:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
  GIVEN("A pattern without java prefix, with descriptor, with regex in package")
  {
    const std::string pattern = R"(\w+.Class.methodName:\(\)V)";
    const std::vector<irep_idt> expected = {
      "java::pack.Class.methodName:()V", "java::another.Class.methodName:()V"};
    require_result_for_pattern(pattern, expected, symbol_table);
  }
}
