/*******************************************************************\

 Module: Java string library preprocess.
         Test for converting an expression to a string expression.

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <util/expr.h>
#include <util/std_code.h>
#include <util/namespace.h>
#include <java_bytecode/java_object_factory.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_root_class.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <iostream>

SCENARIO(
  "Generate string object",
  "[core][java_bytecode][java_object_factor][gen_nondet_string_init]")
{
  GIVEN("an expression, a location, and a symbol table")
  {
    source_locationt loc;
    symbol_tablet symbol_table;
    register_language(new_java_bytecode_language);

    // Add java.lang.Object to symbol table
    symbolt jlo_sym;
    jlo_sym.name = "java::java.lang.Object";
    jlo_sym.type = struct_typet();
    jlo_sym.is_type = true;
    java_root_class(jlo_sym);
    bool failed = symbol_table.add(jlo_sym);
    CHECK_RETURN(!failed);

    // Add java.lang.String to symbol table
    java_string_library_preprocesst preprocess;
    preprocess.add_string_type("java.lang.String", symbol_table);
    namespacet ns(symbol_table);

    // Declare a String named arg
    symbol_typet java_string_type("java::java.lang.String");
    symbol_exprt expr("arg", java_string_type);

    WHEN("Initialisation code for a string is generated")
    {
      const codet code =
        initialize_nondet_string_struct(expr, 20, loc, symbol_table, false);

      THEN("Code is produced")
      {
        std::vector<std::string> code_string;

        const std::regex spaces("\\s+");
        const std::regex numbers("\\$[0-9]*");
        for(auto op : code.operands())
        {
          const std::string line = from_expr(ns, "", op);
          code_string.push_back(
            std::regex_replace(
              std::regex_replace(line, spaces, " "), numbers, ""));
        }

        const std::vector<std::string> reference_code = { // NOLINT
          "int tmp_object_factory;",
          "tmp_object_factory = NONDET(int);",
          "__CPROVER_assume(tmp_object_factory >= 0);",
          "__CPROVER_assume(tmp_object_factory <= 20);",
          "char (*string_data_pointer)[INFINITY()];",
          "string_data_pointer = "
            "ALLOCATE(char [INFINITY()], INFINITY(), false);",
          "char nondet_infinite_array[INFINITY()];",
          "nondet_infinite_array = NONDET(char [INFINITY()]);",
          "*string_data_pointer = nondet_infinite_array;",
          "int return_array;",
          "return_array = cprover_associate_array_to_pointer_func"
            "(*string_data_pointer, *string_data_pointer);",
          "int return_array;",
          "return_array = cprover_associate_length_to_array_func"
            "(*string_data_pointer, tmp_object_factory);",
          "arg = { .@java.lang.Object={ .@class_identifier"
            "=\"java::java.lang.String\", .@lock=false },"
            " .length=tmp_object_factory, "
            ".data=*string_data_pointer };"};

        for(std::size_t i = 0;
            i < code_string.size() && i < reference_code.size();
            ++i)
          REQUIRE(code_string[i] == reference_code[i]);

        REQUIRE(code_string.size() == reference_code.size());
      }
    }
  }
}
