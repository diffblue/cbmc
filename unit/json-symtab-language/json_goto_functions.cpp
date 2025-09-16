/*******************************************************************\

Module: Unit tests for json_goto_functions

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for json_goto_functions

#include <util/json.h>

#include <json-symtab-language/json_goto_functions.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_functions.h>

TEST_CASE(
  "JSON goto functions without body",
  "[core][json-symtab-language][json_goto_functions]")
{
  // Create a simple JSON representation of goto_functions
  json_objectt json_goto_functions;
  json_arrayt functions;

  // Create a simple function
  json_objectt json_function;
  json_function["isHidden"] = jsont::json_boolean(false);

  // Add parameter_identifiers field
  json_arrayt param_ids;
  param_ids.push_back(json_stringt{"param1"});
  json_function["parameterIdentifiers"] = param_ids;

  // Add body field with empty instructions
  json_arrayt instructions;
  json_function["instructions"] = instructions;

  // Add the function to the functions object
  json_function["name"] = json_stringt{"test_function"};
  functions.push_back(json_function);

  // Add the functions object to the goto_functions object
  json_goto_functions["functions"] = functions;

  // Convert JSON to goto_functions
  goto_functionst goto_functions;
  goto_functions_from_json(json_goto_functions, goto_functions);

  // Check that the functions were parsed correctly
  REQUIRE(goto_functions.function_map.size() == 1);
  REQUIRE(
    goto_functions.function_map.find("test_function") !=
    goto_functions.function_map.end());

  const goto_functiont &function =
    goto_functions.function_map.at("test_function");
  REQUIRE(!function.is_hidden());
  REQUIRE(function.parameter_identifiers.size() == 1);
  REQUIRE(function.parameter_identifiers[0] == "param1");
  REQUIRE(function.body.instructions.empty());
}
