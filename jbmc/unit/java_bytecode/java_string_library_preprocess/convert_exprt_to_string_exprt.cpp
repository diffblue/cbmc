/*******************************************************************\

Module: Java string library preprocess.
        Test for converting an expression to a string expression.

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_string_library_preprocess.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/std_code.h>

refined_string_exprt convert_exprt_to_string_exprt_unit_test(
  java_string_library_preprocesst &preprocess,
  const exprt &deref,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  return preprocess.convert_exprt_to_string_exprt(
    deref, loc, symbol_table, init_code);
}

TEST_CASE("Convert exprt to string exprt")
{
  GIVEN("A location, a string expression, and a symbol table")
  {
    source_locationt loc;
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    code_blockt code;
    java_string_library_preprocesst preprocess;
    preprocess.add_string_type("java.lang.String", symbol_table);
    struct_tag_typet java_string_type("java::java.lang.String");
    symbol_exprt expr("a", pointer_type(java_string_type));

    WHEN("String expression is converted to refined string expression")
    {
      refined_string_exprt string_expr =
        convert_exprt_to_string_exprt_unit_test(
          preprocess, expr, loc, symbol_table, code);

      THEN("The type of the returd expression is that of refined strings")
      {
        REQUIRE(string_expr.id() == ID_struct);
        REQUIRE(is_refined_string_type(string_expr.type()));
      }

      THEN("Code is produced")
      {
        register_language(new_java_bytecode_language);

        std::vector<std::string> code_string;
        const std::regex spaces("\\s+");
        const std::regex numbers("\\$[0-9]*");
        for(auto op : code.operands())
        {
          const std::string line = from_expr(ns, "a", op);
          code_string.push_back(
            std::regex_replace(
              std::regex_replace(line, spaces, " "), numbers, ""));
        }

        const std::vector<std::string> reference_code = {
          // NOLINT
          "char *cprover_string_content;",
          "int cprover_string_length;",
          "cprover_string_length = a == null ? 0 : a->length;",
          "cprover_string_content = a->data;"};

        for(std::size_t i = 0;
            i < code_string.size() && i < reference_code.size();
            ++i)
          REQUIRE(code_string[i] == reference_code[i]);

        REQUIRE(code_string.size() == reference_code.size());
      }
    }
  }
}
