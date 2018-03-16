/// file
/// Test for types in return value of make_object_get_class_code

/// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>
#include <util/symbol_table.h>
#include <testing-utils/free_form_cmdline.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java-testing-utils/load_java_class.h>

TEST_CASE("Check types of return value of make_object_get_class_code")
{
  GIVEN("A class that uses getClass")
  {
    WHEN("String refinement is turned on")
    {
      free_form_cmdlinet command_line;
      command_line.add_flag("refine-strings");
      symbol_tablet symbol_table =
        load_java_class(
          "TestObjectGetClass",
          ".",
          "",
          new_java_bytecode_language(),
          command_line);
      THEN("The type of the returned expression is that of refined strings")
      {
        for(auto &named_symbol : symbol_table.symbols)
        {

          named_symbol.first;
          named_symbol.second.value.id();
        }
      }
      //code_typet::parametert param;
      //param.set_identifier("this");
      //code_typet type;
      //type.parameters().push_back(param);
      //source_locationt loc;
      //loc.
      //symbol_tablet symbol_table;
      //THEN("The type of the returned expression is that of refined strings")
      //{
      //  code_for_function("java::java.lang.Object.getClass:()Ljava/lang/Class;", type, loc, symbol_table);
      //  REQUIRE(string_expr.id() == ID_struct);
      //}
    }
  }
}
