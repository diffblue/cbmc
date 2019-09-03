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
  GIVEN("A JSON file containing escaped characters")
  {
    temporary_filet unicode_json_file("cbmc_unit_json_parser_escaped", ".json");
    const std::string unicode_json_path = unicode_json_file();
    {
      std::ofstream unicode_json_out(unicode_json_path);
      unicode_json_out << "{\n"
                       << "  \"doublequote\": \"\\\"\",\n"
                       << "  \"backslash\": \"\\\\\",\n"
                       << "  \"slash\": \"\\/\",\n"
                       << "  \"backspace\": \"\\b\",\n"
                       << "  \"formfeed\": \"\\f\",\n"
                       << "  \"newline\": \"\\n\",\n"
                       << "  \"return\": \"\\r\",\n"
                       << "  \"tab\": \"\\t\",\n"
                       << "  \"several\": \"\\\"\\\\\\/\\b\\f\\n\\r\\t\"\n"
                       << "}\n";
    }
    WHEN("Loading the JSON file with the escaped characters")
    {
      jsont unicode_json;
      const auto unicode_parse_error =
        parse_json(unicode_json_path, null_message_handler, unicode_json);
      THEN("The JSON file should be parsed correctly")
      {
        REQUIRE_FALSE(unicode_parse_error);
        REQUIRE(unicode_json.is_object());

        const json_objectt &json_object = to_json_object(unicode_json);

        REQUIRE(json_object.find("doublequote") != json_object.end());
        REQUIRE(json_object["doublequote"].value == "\"");

        REQUIRE(json_object.find("backslash") != json_object.end());
        REQUIRE(json_object["backslash"].value == "\\");

        REQUIRE(json_object.find("slash") != json_object.end());
        REQUIRE(json_object["slash"].value == "/");

        REQUIRE(json_object.find("backspace") != json_object.end());
        REQUIRE(json_object["backspace"].value == "\b");

        REQUIRE(json_object.find("formfeed") != json_object.end());
        REQUIRE(json_object["formfeed"].value == "\f");

        REQUIRE(json_object.find("newline") != json_object.end());
        REQUIRE(json_object["newline"].value == "\n");

        REQUIRE(json_object.find("return") != json_object.end());
        REQUIRE(json_object["return"].value == "\r");

        REQUIRE(json_object.find("tab") != json_object.end());
        REQUIRE(json_object["tab"].value == "\t");

        REQUIRE(json_object.find("several") != json_object.end());
        REQUIRE(json_object["several"].value == "\"\\/\b\f\n\r\t");
      }
    }
  }
}

TEST_CASE("json equality", "[core][util][json]")
{
  SECTION("null")
  {
    REQUIRE(jsont::null_json_object == jsont::null_json_object);
  }

  SECTION("boolean")
  {
    REQUIRE(jsont::json_boolean(false) == jsont::json_boolean(false));
    REQUIRE(jsont::json_boolean(true) == jsont::json_boolean(true));
    REQUIRE_FALSE(jsont::json_boolean(true) == jsont::json_boolean(false));
    REQUIRE_FALSE(jsont::json_boolean(false) == jsont::null_json_object);
  }

  SECTION("number")
  {
    REQUIRE(json_numbert("0") == json_numbert("0"));
    REQUIRE(json_numbert("1") == json_numbert("1"));
    REQUIRE(json_numbert("-1") == json_numbert("-1"));
    REQUIRE(json_numbert("1.578") == json_numbert("1.578"));
    REQUIRE_FALSE(json_numbert("0") == json_numbert("1"));
    REQUIRE_FALSE(json_numbert("1") == json_numbert("-1"));
    REQUIRE_FALSE(json_numbert("-1") == json_numbert("1"));
    REQUIRE_FALSE(json_numbert("1.578") == json_numbert("1.5789"));
    REQUIRE_FALSE(json_numbert("0") == jsont::json_boolean(false));
    REQUIRE_FALSE(jsont::json_boolean(false) == json_numbert("0"));
    REQUIRE_FALSE(json_numbert("0") == jsont::null_json_object);
    REQUIRE_FALSE(jsont::null_json_object == json_numbert("0"));
  }

  SECTION("string")
  {
    REQUIRE(json_stringt("") == json_stringt(""));
    REQUIRE(json_stringt("foo") == json_stringt("foo"));
    REQUIRE(json_stringt("bar") == json_stringt("bar"));
    REQUIRE_FALSE(json_stringt("foo") == json_stringt("bar"));
    REQUIRE_FALSE(json_stringt("bar") == json_stringt("baz"));
    REQUIRE_FALSE(json_stringt("foo") == json_stringt("food"));
    REQUIRE_FALSE(json_stringt("1") == json_numbert("1"));
    REQUIRE_FALSE(json_stringt("true") == jsont::json_boolean("true"));
    REQUIRE_FALSE(json_stringt("") == jsont::json_boolean("false"));
    REQUIRE_FALSE(json_stringt("") == jsont::null_json_object);
  }

  SECTION("array")
  {
    REQUIRE(json_arrayt{} == json_arrayt{});
    REQUIRE(
      json_arrayt{jsont::null_json_object} ==
      json_arrayt{jsont::null_json_object});
    REQUIRE(
      json_arrayt{json_numbert{"9"}, json_numbert{"6"}} ==
      json_arrayt{json_numbert{"9"}, json_numbert{"6"}});
    REQUIRE(
      json_arrayt{
        json_stringt{"foo"}, json_stringt{"bar"}, json_stringt{"baz"}} ==
      json_arrayt{
        json_stringt{"foo"}, json_stringt{"bar"}, json_stringt{"baz"}});

    // different lengths
    REQUIRE_FALSE(
      json_arrayt{json_stringt{"foo"}, json_stringt{"bar"}} ==
      json_arrayt{
        json_stringt{"foo"}, json_stringt{"bar"}, json_stringt{"baz"}});
    // different elements
    REQUIRE_FALSE(
      json_arrayt{
        json_stringt{"foo"}, json_stringt{"bar"}, json_stringt{"foo"}} ==
      json_arrayt{
        json_stringt{"foo"}, json_stringt{"bar"}, json_stringt{"baz"}});
    // different kind
    REQUIRE_FALSE(json_arrayt{} == jsont::json_boolean(false));
    REQUIRE_FALSE(json_arrayt{} == jsont::null_json_object);
  }

  SECTION("object")
  {
    REQUIRE(json_objectt{} == json_objectt{});
    REQUIRE(
      json_objectt{{"key", json_stringt{"value"}}} ==
      json_objectt{{"key", json_stringt{"value"}}});
    REQUIRE(
      json_objectt{{"key1", json_stringt{"value1"}},
                   {"key2", json_stringt{"value2"}}} ==
      json_objectt{{"key1", json_stringt{"value1"}},
                   {"key2", json_stringt{"value2"}}});

    // Extra property
    REQUIRE_FALSE(
      json_objectt{{"key1", json_stringt{"value1"}},
                   {"key2", json_stringt{"value2"}},
                   {"key3", json_stringt{"value3"}}} ==
      json_objectt{{"key1", json_stringt{"value1"}},
                   {"key2", json_stringt{"value2"}}});
    // different field values
    REQUIRE_FALSE(
      json_objectt{{"key1", json_stringt{"foo"}},
                   {"key2", json_stringt{"bar"}}} ==
      json_objectt{{"key1", json_stringt{"foo"}},
                   {"key2", json_stringt{"baz"}}});
    // different kind
    REQUIRE_FALSE(json_objectt{} == json_arrayt{});
    REQUIRE_FALSE(json_objectt{} == jsont::null_json_object);
  }
}
