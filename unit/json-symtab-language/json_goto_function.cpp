/*******************************************************************\

Module: Unit tests for json_goto_function

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for json_goto_function

#include <util/json.h>

#include <json-symtab-language/json_goto_function.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "JSON goto function without body",
  "[core][json-symtab-language][json_goto_function]")
{
  // Create a simple JSON representation of a goto_function
  json_objectt json_function;

  // Add is_hidden field
  json_function["isHidden"] = jsont::json_boolean(true);

  // Add parameter_identifiers field
  json_arrayt param_ids;
  param_ids.push_back(json_stringt{"param1"});
  param_ids.push_back(json_stringt{"param2"});
  json_function["parameterIdentifiers"] = param_ids;

  // Add body field with empty instructions
  json_arrayt instructions;
  json_function["instructions"] = instructions;

  // Convert JSON to goto_function
  goto_functiont function = goto_function_from_json(json_function);

  // Check that the function was parsed correctly
  REQUIRE(function.is_hidden());
  REQUIRE(function.parameter_identifiers.size() == 2);
  REQUIRE(function.parameter_identifiers[0] == "param1");
  REQUIRE(function.parameter_identifiers[1] == "param2");
  REQUIRE(!function.body_available());
}
