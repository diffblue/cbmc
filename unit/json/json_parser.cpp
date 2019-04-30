/*******************************************************************\

Module: Example Catch Tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <fstream>
#include <json/json_parser.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>
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

            const json_objectt &json_object = to_json_object(valid_json);
            REQUIRE(json_object.find("hello") != json_object.end());
            REQUIRE(json_object["hello"].value == "world");
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

        const json_objectt &json_object = to_json_object(valid_json);
        REQUIRE(json_object.find("hello") != json_object.end());
        REQUIRE(json_object["hello"].value == "world");
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
  GIVEN("A JSON file containing hexadecimal Unicode symbols")
  {
    temporary_filet unicode_json_file("cbmc_unit_json_parser_unicode", ".json");
    const std::string unicode_json_path = unicode_json_file();
    {
      std::ofstream unicode_json_out(unicode_json_path);
      unicode_json_out << "{\n"
                       << "  \"one\": \"\\u0001\",\n"
                       << "  \"latin\": \"\\u0042\",\n"
                       << "  \"grave\": \"\\u00E0\",\n"
                       << "  \"trema\": \"\\u00FF\",\n"
                       << "  \"high\": \"\\uFFFF\",\n"
                       << "  \"several\": \"a\\u0041b\\u2FC3\\uFFFF\"\n"
                       << "}\n";
    }
    WHEN("Loading the JSON file with the Unicode symbols")
    {
      jsont unicode_json;
      const auto unicode_parse_error =
        parse_json(unicode_json_path, null_message_handler, unicode_json);
      THEN("The JSON file should be parsed correctly")
      {
        REQUIRE_FALSE(unicode_parse_error);
        REQUIRE(unicode_json.is_object());

        const json_objectt &json_object = to_json_object(unicode_json);

        REQUIRE(json_object.find("one") != json_object.end());
        REQUIRE(json_object["one"].value.size() == 1);
        REQUIRE(json_object["one"].value == u8"\u0001");

        REQUIRE(json_object.find("latin") != json_object.end());
        REQUIRE(json_object["latin"].value == "B");

        REQUIRE(json_object.find("grave") != json_object.end());
        REQUIRE(json_object["grave"].value == "à");

        REQUIRE(json_object.find("trema") != json_object.end());
        REQUIRE(json_object["trema"].value == "ÿ");

        REQUIRE(json_object.find("high") != json_object.end());
        REQUIRE(json_object["high"].value == u8"\uFFFF");

        REQUIRE(json_object.find("several") != json_object.end());
        REQUIRE(json_object["several"].value == u8"aAb\u2FC3\uFFFF");
      }
    }
  }
}
