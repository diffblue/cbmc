/*******************************************************************\

Module: Extended unit tests for json_goto_functions

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Extended unit tests for json_goto_functions including error handling

#include <util/exception_utils.h>
#include <util/json.h>
#include <util/json_irep.h>

#include <json-symtab-language/json_goto_functions.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_functions.h>

TEST_CASE(
  "JSON goto functions without body (extended)",
  "[core][json-symtab-language][json_goto_functions]")
{
  // Create a JSON representation of goto_functions with multiple functions
  json_objectt json_goto_functions;
  json_arrayt functions;

  // Create first function
  json_objectt json_function1;
  json_function1["isHidden"] = jsont::json_boolean(false);

  // Add parameter_identifiers field
  json_arrayt param_ids1;
  param_ids1.push_back(json_stringt{"param1"});
  json_function1["parameterIdentifiers"] = param_ids1;

  // Add body field with empty instructions
  json_arrayt instructions1;
  json_function1["instructions"] = instructions1;

  // Create second function
  json_objectt json_function2;
  json_function2["isHidden"] = jsont::json_boolean(true);

  // Add parameter_identifiers field
  json_arrayt param_ids2;
  param_ids2.push_back(json_stringt{"param1"});
  param_ids2.push_back(json_stringt{"param2"});
  json_function2["parameterIdentifiers"] = param_ids2;

  // Add body field with instructions
  json_arrayt instructions2;

  // Add a SKIP instruction
  json_objectt skip_instruction;
  skip_instruction["instructionId"] = json_stringt{"SKIP"};
  skip_instruction["locationNumber"] = json_numbert{"1"};
  instructions2.push_back(skip_instruction);

  json_function2["instructions"] = instructions2;

  // Add the functions to the functions object
  json_function1["name"] = json_stringt{"function1"};
  functions.push_back(json_function1);
  json_function2["name"] = json_stringt{"function2"};
  functions.push_back(json_function2);

  // Add the functions object to the goto_functions object
  json_goto_functions["functions"] = functions;

  // Convert JSON to goto_functions
  goto_functionst goto_functions;
  goto_functions_from_json(json_goto_functions, goto_functions);

  // Check that the functions were parsed correctly
  REQUIRE(goto_functions.function_map.size() == 2);
  REQUIRE(
    goto_functions.function_map.find("function1") !=
    goto_functions.function_map.end());
  REQUIRE(
    goto_functions.function_map.find("function2") !=
    goto_functions.function_map.end());

  // Check function1
  const goto_functiont &function1 = goto_functions.function_map.at("function1");
  REQUIRE(!function1.is_hidden());
  REQUIRE(function1.parameter_identifiers.size() == 1);
  REQUIRE(function1.parameter_identifiers[0] == "param1");
  REQUIRE(function1.body.instructions.empty());

  // Check function2
  const goto_functiont &function2 = goto_functions.function_map.at("function2");
  REQUIRE(function2.is_hidden());
  REQUIRE(function2.parameter_identifiers.size() == 2);
  REQUIRE(function2.parameter_identifiers[0] == "param1");
  REQUIRE(function2.parameter_identifiers[1] == "param2");
  REQUIRE(function2.body.instructions.size() == 1);
  REQUIRE(function2.body.instructions.front().is_skip());
}

TEST_CASE(
  "JSON goto functions error handling",
  "[core][json-symtab-language][json_goto_functions]")
{
  SECTION("Non-object input")
  {
    jsont json_string = json_stringt{"not an object"};
    goto_functionst goto_functions;

    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_string, goto_functions),
      deserialization_exceptiont);
  }

  SECTION("Missing functions key")
  {
    json_objectt json_goto_functions;
    // No "functions" key

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);
  }

  SECTION("Invalid functions type")
  {
    json_objectt json_goto_functions;
    json_goto_functions["functions"] = json_stringt{"not an object"};

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);
  }

  SECTION("Invalid function object")
  {
    json_objectt json_goto_functions;
    json_arrayt functions;

    // Add an invalid function (string instead of object)
    functions.push_back(json_stringt{"not an object"});

    json_goto_functions["functions"] = functions;

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);
  }

  SECTION("Function with invalid parameter_identifiers")
  {
    json_objectt json_goto_functions;
    json_arrayt functions;

    json_objectt json_function;
    json_function["parameterIdentifiers"] = json_stringt{"not an array"};

    json_function["name"] = json_stringt{"invalid_function"};
    functions.push_back(json_function);
    json_goto_functions["functions"] = functions;

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);
  }
}

TEST_CASE(
  "JSON goto functions with non-trivial structure",
  "[core][json-symtab-language][json_goto_functions]")
{
  // Create a JSON representation of goto_functions with a complex function
  json_objectt json_goto_functions;
  json_arrayt functions;

  // Create a function with a more complex structure
  json_objectt json_function;

  // Add body field with instructions
  json_arrayt instructions;

  // Add a GOTO instruction with a target
  json_objectt goto_instruction;
  goto_instruction["instructionId"] = json_stringt{"GOTO"};
  goto_instruction["guard"] = json_irept{true}.convert_from_irep(true_exprt{});
  goto_instruction["locationNumber"] = json_numbert{"1"};

  // Add targets array pointing to the second instruction
  json_arrayt targets;
  targets.push_back(json_numbert{"2"});
  goto_instruction["targets"] = targets;

  // Add a source location
  json_objectt goto_location;
  goto_location["file"] = json_stringt{"test.c"};
  goto_location["line"] = json_stringt{"10"};
  goto_instruction["sourceLocation"] = goto_location;

  instructions.push_back(goto_instruction);

  // Add a SKIP instruction as the target
  json_objectt skip_instruction;
  skip_instruction["instructionId"] = json_stringt{"SKIP"};
  skip_instruction["locationNumber"] = json_numbert{"2"};

  // Add a source location
  json_objectt skip_location;
  skip_location["file"] = json_stringt{"test.c"};
  skip_location["line"] = json_stringt{"11"};
  skip_instruction["sourceLocation"] = skip_location;

  instructions.push_back(skip_instruction);

  // Add an END_FUNCTION instruction
  json_objectt end_function_instruction;
  end_function_instruction["instructionId"] = json_stringt{"END_FUNCTION"};
  end_function_instruction["locationNumber"] = json_numbert{"3"};
  instructions.push_back(end_function_instruction);

  json_function["instructions"] = instructions;

  // Add the function to the functions object
  json_function["name"] = json_stringt{"complex_function"};
  functions.push_back(json_function);

  // Add the functions object to the goto_functions object
  json_goto_functions["functions"] = functions;

  // Convert JSON to goto_functions
  goto_functionst goto_functions;
  goto_functions_from_json(json_goto_functions, goto_functions);

  // Check that the function was parsed correctly
  REQUIRE(goto_functions.function_map.size() == 1);
  REQUIRE(
    goto_functions.function_map.find("complex_function") !=
    goto_functions.function_map.end());

  const goto_functiont &function =
    goto_functions.function_map.at("complex_function");
  REQUIRE(function.body.instructions.size() == 3);

  // Check the first instruction and its target
  auto it = function.body.instructions.begin();
  REQUIRE(it->is_goto());
  REQUIRE(it->source_location().get_file() == "test.c");
  REQUIRE(it->source_location().get_line() == "10");
  REQUIRE(it->targets.size() == 1);

  // The target should be the second instruction
  auto target_it = it->targets.front();
  REQUIRE(target_it->is_skip());
  REQUIRE(target_it->source_location().get_file() == "test.c");
  REQUIRE(target_it->source_location().get_line() == "11");

  // Check that the location numbers, target numbers, etc. were computed
  REQUIRE(!function.body.instructions.begin()->is_target());
  REQUIRE(std::next(function.body.instructions.begin())->is_target());
}
