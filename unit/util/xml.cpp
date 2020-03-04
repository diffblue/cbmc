/*******************************************************************\

Module: Unit tests for xmlt

Author: Thomas Kiley

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/xml.h>

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
