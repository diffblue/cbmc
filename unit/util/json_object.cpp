/*******************************************************************\

Module: Catch tests for json_objectt

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/json.h>
#include <util/optional.h>
#include <util/optional_utils.h>

#include <algorithm>
#include <iterator>

SCENARIO(
  "Test that json_objectt is compatible with STL algorithms",
  "[core][util][json]")
{
  GIVEN("An empty json_objectt")
  {
    json_objectt object;
    THEN("std::transform can be used to insert into the json_object.")
    {
      const std::vector<std::string> input_values = {"one", "two", "three"};
      const std::insert_iterator<json_objectt> insert_it =
        std::inserter(object, object.end());
      std::transform(
        input_values.begin(),
        input_values.end(),
        insert_it,
        [](const std::string &number) {
          return make_pair(number, json_stringt{number});
        });

      const optionalt<jsont> one = optional_lookup(object, "one");
      REQUIRE(one);
      REQUIRE(one->value == "one");
      const optionalt<jsont> two = optional_lookup(object, "two");
      REQUIRE(two);
      REQUIRE(two->value == "two");
      const optionalt<jsont> three = optional_lookup(object, "three");
      REQUIRE(three);
      REQUIRE(three->value == "three");
    }
  }
}
