/*******************************************************************\

Module: Catch tests for json_arrayt

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/constructor_of.h>
#include <util/json.h>
#include <util/range.h>

#include <string>
#include <vector>

SCENARIO(
  "Test that json_arrayt can be constructed from an initializer list.",
  "[core][util][json]")
{
  GIVEN("A json_arrayt constructed from an initializer list.")
  {
    const json_arrayt array{
      json_stringt{"one"}, json_numbert{"2"}, json_stringt{"three"}};
    THEN("The elements of the `json_arrayt` match the initialiser list.")
    {
      auto it = array.begin();
      REQUIRE(it->kind == jsont::kindt::J_STRING);
      REQUIRE(it->value == "one");
      ++it;
      REQUIRE(it->kind == jsont::kindt::J_NUMBER);
      REQUIRE(it->value == "2");
      ++it;
      REQUIRE(it->kind == jsont::kindt::J_STRING);
      REQUIRE(it->value == "three");
      ++it;
      REQUIRE(it == array.end());
    }
  }
}

SCENARIO(
  "Test that json_arrayt can be constructed using `ranget`",
  "[core][util][json]")
{
  GIVEN("A vector of strings.")
  {
    const std::vector<std::string> input{"foo", "bar"};
    THEN(
      "A json_arrayt can be constructed from the vector of strings using range "
      "and map.")
    {
      const json_arrayt array = make_range(input)
                                  .map(constructor_of<json_stringt>())
                                  .collect<json_arrayt>();
      auto it = array.begin();
      REQUIRE(it->kind == jsont::kindt::J_STRING);
      REQUIRE(it->value == "foo");
      ++it;
      REQUIRE(it->kind == jsont::kindt::J_STRING);
      REQUIRE(it->value == "bar");
      ++it;
      REQUIRE(it == array.end());
    }
  }
}
