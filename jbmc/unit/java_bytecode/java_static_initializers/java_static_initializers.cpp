/*******************************************************************\

Module: Unit tests for java_static_initializers

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_static_initializers.h>

#include <java_bytecode/ci_lazy_methods_needed.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>

#include <testing-utils/expr_query.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/json.h>
#include <util/symbol_table.h>

SCENARIO("is_clinit_function", "[core][java_static_initializers]")
{
  GIVEN("A function id that represents a clinit")
  {
    THEN("is_clinit_function should return true.")
    {
      const std::string input = "com.something.package.TestClass.<clinit>:()V";
      REQUIRE(is_clinit_function(input));
    }
  }
  GIVEN("A function id that does not represent a clinit")
  {
    THEN("is_clinit_function should return false.")
    {
      const std::string input =
        "com.something.package.TestClass.<notclinit>:()V";
      REQUIRE_FALSE(is_clinit_function(input));
    }
  }
}

SCENARIO(
  "is_user_specified_clinit_function",
  "[core][java_static_initializers]")
{
  GIVEN("A function id that represents a user-specified clinit")
  {
    THEN("is_user_specified_clinit_function should return true.")
    {
      const std::string input =
        "com.something.package.TestClass.<user_specified_clinit>";
      REQUIRE(is_user_specified_clinit_function(input));
    }
  }
  GIVEN("A function id that does not represent a user-specified clinit")
  {
    THEN("is_clinit_function should return false.")
    {
      const std::string input = "com.something.package.TestClass::not_it";
      REQUIRE_FALSE(is_user_specified_clinit_function(input));
    }
  }
}

SCENARIO("get_user_specified_clinit_body", "[core][java_static_initializers]")
{
  json_objectt static_values_json{};
  symbol_tablet symbol_table;
  const std::size_t max_user_array_length = 100;
  std::unordered_map<std::string, object_creation_referencet> references;
  std::unordered_multimap<irep_idt, symbolt> class_to_declared_symbols;

  GIVEN(
    "A class which has no entry in the JSON object but a clinit defined "
    "in the symbol table")
  {
    symbolt clinit_symbol;
    clinit_symbol.name = "java::TestClass.<clinit>:()V";
    symbol_table.insert(clinit_symbol);

    const code_blockt clinit_body = get_user_specified_clinit_body(
      "java::TestClass",
      static_values_json,
      symbol_table,
      {},
      max_user_array_length,
      references,
      class_to_declared_symbols);

    THEN("User provided clinit body is composed of one call to clinit")
    {
      const exprt function_called =
        make_query(clinit_body)[0].as<code_function_callt>().get().function();
      REQUIRE(
        make_query(function_called).as<symbol_exprt>().get().get_identifier() ==
        clinit_symbol.name);
    }
  }
  GIVEN("A class which has no entry in the JSON object and no clinit defined")
  {
    const auto clinit_body = get_user_specified_clinit_body(
      "java::TestClass",
      static_values_json,
      symbol_table,
      {},
      max_user_array_length,
      references,
      class_to_declared_symbols);

    THEN("User provided clinit body is empty")
    {
      REQUIRE(clinit_body == code_blockt{});
    }
  }
  GIVEN(
    "A class which has an entry in the JSON object but no clinit defined "
    "in the symbol table")
  {
    static_values_json["TestClass"] = [] {
      json_objectt entry{};
      entry["field_name"] = json_numbert{"42"};
      return entry;
    }();

    const code_blockt clinit_body = get_user_specified_clinit_body(
      "java::TestClass",
      static_values_json,
      symbol_table,
      {},
      max_user_array_length,
      references,
      class_to_declared_symbols);

    THEN("User provided clinit body is empty")
    {
      REQUIRE(clinit_body == code_blockt{});
    }
  }
  GIVEN("A class which has a static number in the provided JSON")
  {
    static_values_json["TestClass"] = [] {
      json_objectt entry{};
      entry["field_name"] = json_numbert{"42"};
      return entry;
    }();
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "field_name";
      field_symbol.name = "field_name_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    symbol_table.insert([] {
      symbolt clinit_symbol;
      clinit_symbol.name = "java::TestClass.<clinit>:()V";
      set_declaring_class(clinit_symbol, "java::TestClass");
      return clinit_symbol;
    }());
    symbol_table.insert([] {
      symbolt test_class_symbol;
      test_class_symbol.name = "java::TestClass";
      test_class_symbol.type = [] {
        java_class_typet type;
        type.components().emplace_back("field_name", java_int_type());
        return type;
      }();
      return test_class_symbol;
    }());
    const auto clinit_body = get_user_specified_clinit_body(
      "java::TestClass",
      static_values_json,
      symbol_table,
      {},
      max_user_array_length,
      references,
      class_to_declared_symbols);
    THEN("User provided clinit body set the field to the given value")
    {
      auto assignment = make_query(clinit_body)[0].as<code_assignt>().get();
      REQUIRE(
        make_query(assignment.lhs())
          .as<symbol_exprt>()
          .get()
          .get_identifier() == "field_name_for_codet");
      REQUIRE(assignment.rhs() == from_integer(42, java_int_type()));
    }
  }
}
