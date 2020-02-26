/*******************************************************************\

Module: Unit tests for the structed_datat related classes

Author: Thomas Kiley

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/structured_data.h>

TEST_CASE("label", "[core][util][structured_data][label]")
{
  SECTION("Empty label")
  {
    labelt empty_label({});
    REQUIRE(empty_label.camel_case() == "");
    REQUIRE(empty_label.kebab_case() == "");
    REQUIRE(empty_label.snake_case() == "");
    REQUIRE(empty_label.pretty() == "");
  }
  SECTION("Single element")
  {
    labelt empty_label({"hello"});
    REQUIRE(empty_label.camel_case() == "hello");
    REQUIRE(empty_label.kebab_case() == "hello");
    REQUIRE(empty_label.snake_case() == "hello");
    REQUIRE(empty_label.pretty() == "Hello");
  }
  SECTION("Two elements")
  {
    labelt empty_label({"hello", "goodbye"});
    REQUIRE(empty_label.camel_case() == "helloGoodbye");
    REQUIRE(empty_label.kebab_case() == "hello-goodbye");
    REQUIRE(empty_label.snake_case() == "hello_goodbye");
    REQUIRE(empty_label.pretty() == "Hello goodbye");
  }
  SECTION("Odd casing elements")
  {
    labelt empty_label({"HelLo", "Goodbye"});
    REQUIRE(empty_label.camel_case() == "helloGoodbye");
    REQUIRE(empty_label.kebab_case() == "hello-goodbye");
    REQUIRE(empty_label.snake_case() == "hello_goodbye");
    REQUIRE(empty_label.pretty() == "Hello goodbye");
  }
}

TEST_CASE("Label equality", "[core][util][structured_data][label]")
{
  labelt empty_label({});
  labelt single_label({"a"});
  labelt capital_label({"A"});
  labelt b_label({"b"});
  labelt multi_label({"b", "c", "d"});
  labelt multi_label2({"b", "d", "d"});

  REQUIRE(empty_label < single_label);
  REQUIRE(empty_label < capital_label);
  REQUIRE(empty_label < b_label);
  REQUIRE(empty_label < multi_label);
  REQUIRE(empty_label < multi_label2);

  REQUIRE_FALSE(single_label < capital_label);
  REQUIRE_FALSE(capital_label < single_label);

  REQUIRE(single_label < b_label);
  REQUIRE(single_label < multi_label);
  REQUIRE(single_label < multi_label2);

  REQUIRE(capital_label < b_label);
  REQUIRE(capital_label < multi_label);
  REQUIRE(capital_label < multi_label2);

  REQUIRE(b_label < multi_label);
  REQUIRE(b_label < multi_label2);

  REQUIRE(multi_label < multi_label2);
}
