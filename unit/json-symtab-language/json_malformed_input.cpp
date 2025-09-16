/*******************************************************************\

Module: Unit tests for handling malformed JSON input

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for handling malformed JSON input

#include <util/exception_utils.h>
#include <util/json.h>

#include <json-symtab-language/json_goto_function.h>
#include <json-symtab-language/json_goto_functions.h>
#include <json-symtab-language/json_symbol.h>
#include <json-symtab-language/json_symbol_table.h>
#include <json/json_parser.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_functions.h>

TEST_CASE(
  "Malformed JSON input for goto_function",
  "[core][json-symtab-language][json_goto_function]")
{
  SECTION("Malformed JSON - syntax error")
  {
    // This is not valid JSON (missing closing brace)
    std::string malformed_json = R"({
      "body": {
        "instructions": [
          {
            "instructionId": "SKIP"
          }
        ]
      }
    )";

    // Try to parse the malformed JSON
    jsont json;
    std::istringstream stream(malformed_json);
    // This should fail, i.e., return true
    REQUIRE(parse_json(stream, "<inline>", null_message_handler, json) == true);
  }

  SECTION("Malformed JSON - semantic errors")
  {
    // Test 1: Missing required field 'type' in instruction
    json_objectt json_function;
    json_arrayt instructions;

    // Create an instruction without a type field
    json_objectt instruction_without_type;
    // No "instructionId" field

    instructions.push_back(instruction_without_type);
    json_function["instructions"] = instructions;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);

    // Test 2: Invalid instruction type value
    json_objectt json_function2;
    json_arrayt instructions2;

    json_objectt instruction_invalid_type;
    instruction_invalid_type["instructionId"] = json_stringt{"INVALID_TYPE"};
    instruction_invalid_type["locationNumber"] = json_numbert{"1"};

    instructions2.push_back(instruction_invalid_type);
    json_function2["instructions"] = instructions2;

    // This should throw as unknown instruction types are not valid
    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function2), deserialization_exceptiont);

    // Test 3: Invalid target index (negative)
    json_objectt json_function3;
    json_arrayt instructions3;

    json_objectt instruction_negative_target;
    instruction_negative_target["instructionId"] = json_stringt{"GOTO"};
    instruction_negative_target["locationNumber"] = json_numbert{"1"};

    json_arrayt targets;
    targets.push_back(json_numbert{"-1"}); // Negative index
    instruction_negative_target["targets"] = targets;

    instructions3.push_back(instruction_negative_target);
    json_function3["instructions"] = instructions3;

    // This should throw as negative indices are not valid
    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function3), deserialization_exceptiont);

    // Test 4: Target index out of bounds
    json_objectt json_function4;
    json_arrayt instructions4;

    json_objectt instruction_oob_target;
    instruction_oob_target["instructionId"] = json_stringt{"GOTO"};
    instruction_oob_target["locationNumber"] = json_numbert{"1"};

    json_arrayt targets4;
    targets4.push_back(json_numbert{"999"}); // Out of bounds
    instruction_oob_target["targets"] = targets4;

    instructions4.push_back(instruction_oob_target);
    json_function4["instructions"] = instructions4;

    // This should throw as the target index is out of bounds
    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function4), deserialization_exceptiont);
  }
}

TEST_CASE(
  "Malformed JSON input for goto_functions",
  "[core][json-symtab-language][json_goto_functions]")
{
  SECTION("Missing required fields")
  {
    // Test 1: Missing 'functions' field
    json_objectt json_goto_functions;
    // No "functions" field

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);

    // Test 2: 'functions' field is not an object
    json_objectt json_goto_functions2;
    json_goto_functions2["functions"] = json_stringt{"not an object"};

    goto_functionst goto_functions2;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions2, goto_functions2),
      deserialization_exceptiont);
  }

  SECTION("Invalid function objects")
  {
    // Test 1: Function is not an object
    json_objectt json_goto_functions;
    json_objectt functions;

    functions["invalid_function"] = json_stringt{"not an object"};
    json_goto_functions["functions"] = functions;

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);

    // Test 2: Function with invalid body
    json_objectt json_goto_functions2;
    json_objectt functions2;

    json_objectt invalid_function;
    invalid_function["instructions"] = json_stringt{"not an object"};

    functions2["invalid_function"] = invalid_function;
    json_goto_functions2["functions"] = functions2;

    goto_functionst goto_functions2;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions2, goto_functions2),
      deserialization_exceptiont);
  }

  SECTION("Deeply nested errors")
  {
    // Create a JSON structure with an error deep in the hierarchy
    json_objectt json_goto_functions;
    json_arrayt functions;

    json_objectt function;
    json_arrayt instructions;

    // First instruction is valid
    json_objectt valid_instruction;
    valid_instruction["instructionId"] = json_stringt{"SKIP"};
    valid_instruction["locationNumber"] = json_numbert{"1"};
    instructions.push_back(valid_instruction);

    // Second instruction has an invalid guard
    json_objectt invalid_instruction;
    invalid_instruction["instructionId"] = json_stringt{"ASSUME"};
    invalid_instruction["locationNumber"] = json_numbert{"2"};
    invalid_instruction["guard"] = json_numbert{"123"}; // Should be an object
    instructions.push_back(invalid_instruction);

    function["instructions"] = instructions;
    function["name"] = json_stringt{"test_function"};
    functions.push_back(function);
    json_goto_functions["functions"] = functions;

    goto_functionst goto_functions;
    REQUIRE_THROWS_AS(
      goto_functions_from_json(json_goto_functions, goto_functions),
      deserialization_exceptiont);
  }
}

TEST_CASE(
  "Edge cases for JSON parsing",
  "[core][json-symtab-language][json_goto_function]")
{
  SECTION("Empty objects and arrays")
  {
    // Test 1: Empty function object
    json_objectt empty_function;

    // This should not throw, but create an empty function
    goto_functiont function = goto_function_from_json(empty_function);
    REQUIRE(function.body.instructions.empty());
    REQUIRE(function.parameter_identifiers.empty());
    REQUIRE(!function.is_hidden());

    // Test 2: Empty body
    json_objectt json_function;
    json_function["instructions"] = json_arrayt{};

    // This should not throw
    goto_functiont function2 = goto_function_from_json(json_function);
    REQUIRE(function2.body.instructions.empty());

    // Test 3: Empty instructions array
    json_objectt json_function3;
    json_arrayt empty_instructions;
    json_function3["instructions"] = empty_instructions;

    // This should not throw
    goto_functiont function3 = goto_function_from_json(json_function3);
    REQUIRE(function3.body.instructions.empty());
  }

  SECTION("Unusual but valid JSON")
  {
    // Test 1: Very large instruction array
    json_objectt json_function;
    json_arrayt instructions;

    // Add 1000 SKIP instructions
    for(int i = 0; i < 1000; i++)
    {
      json_objectt skip_instruction;
      skip_instruction["instructionId"] = json_stringt{"SKIP"};
      skip_instruction["locationNumber"] = json_numbert{std::to_string(i)};
      instructions.push_back(skip_instruction);
    }

    json_function["instructions"] = instructions;

    // This should not throw
    goto_functiont function = goto_function_from_json(json_function);
    REQUIRE(function.body.instructions.size() == 1000);

    // Test 2: Very long parameter identifiers array
    json_objectt json_function2;
    json_arrayt param_ids;

    // Add 1000 parameter identifiers
    for(int i = 0; i < 1000; i++)
    {
      param_ids.push_back(json_stringt{"param" + std::to_string(i)});
    }

    json_function2["parameterIdentifiers"] = param_ids;

    // This should not throw
    goto_functiont function2 = goto_function_from_json(json_function2);
    REQUIRE(function2.parameter_identifiers.size() == 1000);
  }
}
