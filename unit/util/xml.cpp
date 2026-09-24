/*******************************************************************\

Module: Unit tests for xmlt

Author: Thomas Kiley

\*******************************************************************/

#include <util/xml.h>

#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("xml_equal", "[core][util][xml]")
{
  SECTION("Empty xml")
  {
    xmlt a;
    xmlt b;
    REQUIRE(a == b);
    REQUIRE_FALSE(a != b);
  }
  SECTION("Matching node")
  {
    xmlt a{"a"};
    a.data = "hello";
    a.attributes = {{"a", "b"}, {"b", "c"}};
    xmlt b{"a"};
    b.data = "hello";
    b.attributes = {{"a", "b"}, {"b", "c"}};

    REQUIRE(a == b);
    REQUIRE_FALSE(a != b);
  }
  SECTION("non-matching node")
  {
    xmlt a{"a"};
    a.data = "hello";
    a.attributes = {{"a", "b"}, {"b", "c"}};
    SECTION("Different name")
    {
      xmlt b{"b"};
      b.data = "hello";
      b.attributes = {{"a", "b"}, {"b", "c"}};

      REQUIRE_FALSE(a == b);
      REQUIRE(a != b);
    }
    SECTION("Different data")
    {
      xmlt b{"b"};
      b.data = "world";
      b.attributes = {{"a", "b"}, {"b", "c"}};

      REQUIRE_FALSE(a == b);
      REQUIRE(a != b);
    }
    SECTION("Different attributes")
    {
      xmlt b{"b"};
      b.data = "world";
      b.attributes = {{"a", "b"}, {"b", "d"}};

      REQUIRE_FALSE(a == b);
      REQUIRE(a != b);
    }
  }
  SECTION("Matching children")
  {
    xmlt a{"a"};
    a.elements = {xmlt{"b"}};
    xmlt b{"a"};
    b.elements = {xmlt{"b"}};

    REQUIRE(a == b);
    REQUIRE_FALSE(a != b);
  }
  SECTION("Non-matching children")
  {
    xmlt a{"a"};
    a.elements = {xmlt{"b"}};
    SECTION("Different child")
    {
      xmlt b{"a"};
      a.elements = {xmlt{"c"}};

      REQUIRE_FALSE(a == b);
      REQUIRE(a != b);
    }
    SECTION("Different sub child")
    {
      xmlt b{"a"};
      xmlt sub_child{"b"};
      sub_child.elements = {xmlt{"d"}};
      a.elements = {sub_child};

      REQUIRE_FALSE(a == b);
      REQUIRE(a != b);
    }
  }
}

TEST_CASE("xml_escape_nonprintable", "[core][util][xml]")
{
  SECTION("Escaping non-printable characters in attributes")
  {
    xmlt node{"test"};
    node.set_attribute("value", std::string("\x00\x01\x02\x1F", 4));

    std::ostringstream out;
    node.output(out);

    std::string result = out.str();
    // Characters invalid in XML 1.0 are encoded as C-style escapes
    REQUIRE(result.find("\\0") != std::string::npos);
    REQUIRE(result.find("\\x01") != std::string::npos);
    REQUIRE(result.find("\\x02") != std::string::npos);
    REQUIRE(result.find("\\x1f") != std::string::npos);
  }

  SECTION("Escaping non-printable characters in data")
  {
    xmlt node{"test"};
    node.data = std::string("\x00\x01\x02\x1F", 4);

    std::ostringstream out;
    node.output(out);

    std::string result = out.str();
    // Characters invalid in XML 1.0 are encoded as C-style escapes
    REQUIRE(result.find("\\0") != std::string::npos);
    REQUIRE(result.find("\\x01") != std::string::npos);
    REQUIRE(result.find("\\x02") != std::string::npos);
    REQUIRE(result.find("\\x1f") != std::string::npos);
  }

  SECTION("Valid XML 1.0 control characters use numeric references")
  {
    xmlt node{"test"};
    node.set_attribute("value", std::string("\x09", 1));

    std::ostringstream out;
    node.output(out);

    std::string result = out.str();
    // TAB is valid in XML 1.0 and uses numeric character reference
    REQUIRE(result.find("&#9;") != std::string::npos);
  }

  SECTION("Backslashes are escaped")
  {
    xmlt node{"test"};
    node.set_attribute("value", "back\\slash");

    std::ostringstream out;
    node.output(out);

    std::string result = out.str();
    REQUIRE(result.find("back\\\\slash") != std::string::npos);
  }

  SECTION("Standard printable characters unchanged")
  {
    xmlt node{"test"};
    node.set_attribute("value", "Hello World!");

    std::ostringstream out;
    node.output(out);

    std::string result = out.str();
    REQUIRE(result.find("Hello World!") != std::string::npos);
  }
}
