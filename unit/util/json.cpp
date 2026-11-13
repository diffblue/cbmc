/*******************************************************************\

Module: Unit tests for JSON parser

Author: Daniel Kroening

\*******************************************************************/

#include <json/json_parser.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("Parse empty JSON object", "[core][json][json_parser]")
{
  std::istringstream in("{}");
  jsont json;

  bool result = parse_json(in, "", null_message_handler, json);

  REQUIRE(result == false); // false means success
  REQUIRE(json.is_object());
}

TEST_CASE("Parse JSON with string", "[core][json][json_parser]")
{
  std::istringstream in(R"({"key": "value"})");
  jsont json;

  bool result = parse_json(in, "", null_message_handler, json);

  REQUIRE(result == false); // false means success
  REQUIRE(json.is_object());
}

TEST_CASE("Parse JSON array", "[core][json][json_parser]")
{
  std::istringstream in("[1, 2, 3]");
  jsont json;

  bool result = parse_json(in, "", null_message_handler, json);

  REQUIRE(result == false); // false means success
  REQUIRE(json.is_array());
}

TEST_CASE("Parse JSON with number", "[core][json][json_parser]")
{
  std::istringstream in(R"({"number": 42})");
  jsont json;

  bool result = parse_json(in, "", null_message_handler, json);

  REQUIRE(result == false); // false means success
  REQUIRE(json.is_object());
}

TEST_CASE("Parse invalid JSON", "[core][json][json_parser]")
{
  std::istringstream in("{invalid}");
  jsont json;

  bool result = parse_json(in, "", null_message_handler, json);

  REQUIRE(result == true); // true means error
}
