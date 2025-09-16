/*******************************************************************\

Module: Extended unit tests for json_goto_function

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Extended unit tests for json_goto_function including error handling

#include <util/exception_utils.h>
#include <util/json.h>
#include <util/json_irep.h>

#include <json-symtab-language/json_goto_function.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "JSON goto function without body (extended)",
  "[core][json-symtab-language][json_goto_function]")
{
  // Create a JSON representation of a goto_function with instructions
  json_objectt json_function;

  // Add parameter_identifiers field
  json_arrayt param_ids;
  param_ids.push_back(json_stringt{"param1"});
  param_ids.push_back(json_stringt{"param2"});
  json_function["parameterIdentifiers"] = param_ids;

  // Add body field with instructions
  json_arrayt instructions;

  // Add a SKIP instruction
  json_objectt skip_instruction;
  skip_instruction["instructionId"] = json_stringt{"SKIP"};
  skip_instruction["locationNumber"] = json_numbert{"1"};

  // Add a source location
  json_objectt location;
  location["file"] = json_stringt{"test.c"};
  location["line"] = json_stringt{"10"};
  location["column"] = json_stringt{"5"};
  skip_instruction["sourceLocation"] = location;

  // Add labels
  json_arrayt labels;
  labels.push_back(json_stringt{"label1"});
  labels.push_back(json_stringt{"label2"});
  skip_instruction["labels"] = labels;

  instructions.push_back(skip_instruction);

  // Add an END_FUNCTION instruction
  json_objectt end_function_instruction;
  end_function_instruction["instructionId"] = json_stringt{"END_FUNCTION"};
  end_function_instruction["locationNumber"] = json_numbert{"2"};

  instructions.push_back(end_function_instruction);

  json_function["instructions"] = instructions;

  // Convert JSON to goto_function
  goto_functiont function = goto_function_from_json(json_function);

  // Check that the function was parsed correctly
  REQUIRE(function.parameter_identifiers.size() == 2);
  REQUIRE(function.parameter_identifiers[0] == "param1");
  REQUIRE(function.parameter_identifiers[1] == "param2");
  REQUIRE(function.body.instructions.size() == 2);

  // Check the first instruction
  auto it = function.body.instructions.begin();
  REQUIRE(it->is_skip());
  REQUIRE(it->source_location().get_file() == "test.c");
  REQUIRE(it->source_location().get_line() == "10");
  REQUIRE(it->labels.size() == 2);
  REQUIRE(it->labels.front() == "label1");
  REQUIRE(it->labels.back() == "label2");

  // Check the second instruction
  ++it;
  REQUIRE(it->is_end_function());
}

TEST_CASE(
  "JSON goto function (non-trivial)",
  "[core][json-symtab-language][json_goto_function]")
{
  // Create a JSON representation of a goto_function with instructions and
  // targets
  json_objectt json_function;

  // Add body field with instructions
  json_arrayt instructions;

  // Add a GOTO instruction with a target
  json_objectt goto_instruction;
  goto_instruction["instructionId"] = json_stringt{"GOTO"};
  goto_instruction["guard"] = json_irept{true}.convert_from_irep(true_exprt{});
  goto_instruction["locationNumber"] = json_numbert{"0"};

  // Add targets array pointing to the second instruction
  json_arrayt targets;
  targets.push_back(json_numbert{"1"});
  goto_instruction["targets"] = targets;

  instructions.push_back(goto_instruction);

  // Add a SKIP instruction as the target
  json_objectt skip_instruction;
  skip_instruction["instructionId"] = json_stringt{"SKIP"};
  skip_instruction["locationNumber"] = json_numbert{"1"};
  instructions.push_back(skip_instruction);

  // Add an END_FUNCTION instruction
  json_objectt end_function_instruction;
  end_function_instruction["instructionId"] = json_stringt{"END_FUNCTION"};
  end_function_instruction["locationNumber"] = json_numbert{"2"};
  instructions.push_back(end_function_instruction);

  json_function["instructions"] = instructions;

  // Convert JSON to goto_function
  goto_functiont function = goto_function_from_json(json_function);

  // Check that the function was parsed correctly
  REQUIRE(function.body.instructions.size() == 3);

  // Check the first instruction and its target
  auto it = function.body.instructions.begin();
  REQUIRE(it->is_goto());
  REQUIRE(it->targets.size() == 1);

  // The target should be the second instruction
  auto target_it = it->targets.front();
  REQUIRE(target_it->is_skip());
}

TEST_CASE(
  "JSON goto function (non-trivial 2)",
  "[core][json-symtab-language][json_goto_function]")
{
  // Create a JSON representation of a goto_function with code and guard
  json_objectt json_function;

  // Add body field with instructions
  json_arrayt instructions;

  // Add an ASSIGN instruction with code
  json_objectt assign_instruction;
  assign_instruction["instructionId"] = json_stringt{"ASSIGN"};
  assign_instruction["locationNumber"] = json_numbert{"1"};

  // Create a simple assignment code: x = 42
  json_objectt code;
  code["id"] = json_stringt{"code"};
  code["namedSub"] =
    json_objectt{{"statement", json_objectt{{"id", json_stringt{"assign"}}}}};

  json_objectt lhs;
  lhs["id"] = json_stringt{"symbol"};
  lhs["namedSub"] =
    json_objectt{{"identifier", json_objectt{{"id", json_stringt{"x"}}}}};

  json_objectt rhs;
  rhs["id"] = json_stringt{"constant"};
  rhs["namedSub"] =
    json_objectt{{"value", json_objectt{{"id", json_stringt{"42"}}}}};

  code["sub"] = json_arrayt{{lhs, rhs}};

  assign_instruction["code"] = code;

  // Add an ASSUME instruction with guard
  json_objectt assume_instruction;
  assume_instruction["instructionId"] = json_stringt{"ASSUME"};
  assume_instruction["locationNumber"] = json_numbert{"2"};

  // Create a simple guard: x > 0
  json_objectt guard;
  guard["id"] = json_stringt{">"};

  json_objectt op0;
  op0["id"] = json_stringt{"symbol"};
  op0["namedSub"] =
    json_objectt{{"identifier", json_objectt{{"id", json_stringt{"x"}}}}};

  json_objectt op1;
  op1["id"] = json_stringt{"constant"};
  op1["namedSub"] =
    json_objectt{{"value", json_objectt{{"id", json_stringt{"0"}}}}};

  guard["sub"] = json_arrayt{{op0, op1}};

  assume_instruction["guard"] = guard;

  instructions.push_back(assign_instruction);
  instructions.push_back(assume_instruction);

  json_function["instructions"] = instructions;

  // Convert JSON to goto_function
  goto_functiont function = goto_function_from_json(json_function);

  // Check that the function was parsed correctly
  REQUIRE(function.body.instructions.size() == 2);

  // Check the first instruction (ASSIGN)
  auto it = function.body.instructions.begin();
  REQUIRE(it->is_assign());
  REQUIRE(it->code().id() == ID_code);

  // Check the second instruction (ASSUME)
  ++it;
  REQUIRE(it->is_assume());
  REQUIRE(it->condition().id() == ID_gt);
}

TEST_CASE(
  "JSON goto function error handling",
  "[core][json-symtab-language][json_goto_function]")
{
  SECTION("Invalid parameter_identifiers type")
  {
    json_objectt json_function;
    json_function["parameter_identifiers"] = json_stringt{"not an array"};

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Invalid parameter identifier type")
  {
    json_objectt json_function;
    json_arrayt param_ids;
    param_ids.push_back(json_numbert{"123"}); // Should be a string
    json_function["parameter_identifiers"] = param_ids;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Invalid is_hidden type")
  {
    json_objectt json_function;
    json_function["isHidden"] = json_stringt{"not a boolean"};

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Invalid instruction type")
  {
    json_objectt json_function;
    json_arrayt instructions;

    json_objectt instruction;
    instruction["instructionId"] = json_numbert{"123"}; // Should be a string

    instructions.push_back(instruction);
    json_function["instructions"] = instructions;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Invalid targets type")
  {
    json_objectt json_function;
    json_arrayt instructions;

    json_objectt instruction;
    instruction["instructionId"] = json_stringt{"GOTO"};
    instruction["targets"] = json_stringt{"not an array"};

    instructions.push_back(instruction);
    json_function["instructions"] = instructions;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Invalid target index type")
  {
    json_objectt json_function;
    json_arrayt instructions;

    json_objectt instruction;
    instruction["instructionId"] = json_stringt{"GOTO"};

    json_arrayt targets;
    targets.push_back(json_stringt{"not a number"});
    instruction["targets"] = targets;

    instructions.push_back(instruction);
    json_function["instructions"] = instructions;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Target index out of bounds")
  {
    json_objectt json_function;
    json_arrayt instructions;

    json_objectt instruction;
    instruction["instructionId"] = json_stringt{"GOTO"};

    json_arrayt targets;
    targets.push_back(json_numbert{"999"}); // Out of bounds
    instruction["targets"] = targets;

    instructions.push_back(instruction);
    json_function["instructions"] = instructions;

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }

  SECTION("Unexpected key")
  {
    json_objectt json_function;
    json_function["unexpected_key"] = json_stringt{"value"};

    REQUIRE_THROWS_AS(
      goto_function_from_json(json_function), deserialization_exceptiont);
  }
}
