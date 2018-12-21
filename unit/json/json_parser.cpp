/*******************************************************************\

Module: Example Catch Tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <fstream>
#include <json/json_parser.h>
#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>
#include <util/tempfile.h>

SCENARIO("Loading JSON files")
{
  GIVEN("A invalid JSON file and a valid JSON file")
  {
    temporary_filet valid_json_file("cbmc_unit_json_parser_valid", ".json");
    temporary_filet invalid_json_file("cbmc_unit_json_parser_invalid", ".json");
    const std::string valid_json_path = valid_json_file();
    const std::string invalid_json_path = invalid_json_file();
    {
      std::ofstream valid_json_out(valid_json_path);
      valid_json_out << "{\n"
                     << "  \"hello\": \"world\"\n"
                     << "}\n";
    }
    {
      std::ofstream invalid_json_out(invalid_json_path);
      invalid_json_out << "foo\n";
    }

    WHEN("Loading the invalid JSON file")
    {
      jsont invalid_json;
      const auto invalid_parse_error =
        parse_json(invalid_json_path, null_message_handler, invalid_json);
      THEN("An error state should be returned")
      {
        REQUIRE(invalid_parse_error);
        REQUIRE(invalid_json.is_null());
        AND_WHEN("Loading the valid JSON file")
        {
          jsont valid_json;
          const auto valid_parse_error =
            parse_json(valid_json_path, null_message_handler, valid_json);
          THEN("The JSON file should be parsed correctly")
          {
            REQUIRE_FALSE(valid_parse_error);
            REQUIRE(valid_json.is_object());
            REQUIRE(valid_json.object.find("hello") != valid_json.object.end());
            REQUIRE(valid_json.object["hello"].value == "world");
          }
        }
      }
    }
    WHEN("Loading the valid JSON file")
    {
      jsont valid_json;
      const auto valid_parse_error =
        parse_json(valid_json_path, null_message_handler, valid_json);
      THEN("The JSON file should be parsed correctly")
      {
        REQUIRE_FALSE(valid_parse_error);
        REQUIRE(valid_json.is_object());
        REQUIRE(valid_json.object.find("hello") != valid_json.object.end());
        REQUIRE(valid_json.object["hello"].value == "world");
        AND_WHEN("Loading the invalid JSON file")
        {
          jsont invalid_json;
          const auto invalid_parse_error =
            parse_json(invalid_json_path, null_message_handler, invalid_json);
          THEN("An error state should be returned")
          {
            REQUIRE(invalid_parse_error);
            REQUIRE(invalid_json.is_null());
          }
        }
      }
    }
  }
}
