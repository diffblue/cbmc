/*******************************************************************\

Module: Catch tests for json_objectt

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/json.h>
#include <util/json_irep.h>
#include <util/optional_utils.h>
#include <util/range.h>
#include <util/source_location.h>

#include <testing-utils/use_catch.h>

#include <algorithm>
#include <iterator>
#include <string>
#include <vector>

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

      const std::optional<jsont> one = optional_lookup(object, "one");
      REQUIRE(one);
      REQUIRE(one->value == "one");
      const std::optional<jsont> two = optional_lookup(object, "two");
      REQUIRE(two);
      REQUIRE(two->value == "two");
      const std::optional<jsont> three = optional_lookup(object, "three");
      REQUIRE(three);
      REQUIRE(three->value == "three");
    }
  }
}

SCENARIO(
  "Test that json_objectt can be constructed from an initializer list.",
  "[core][util][json]")
{
  GIVEN("A json_objectt constructed from an initializer list.")
  {
    const json_objectt object{
      {"number", json_numbert{"6"}},
      {"string", json_stringt{"eggs"}},
      {"mice",
       json_objectt{{"number", json_numbert{"3"}},
                    {"string", json_stringt{"blind"}}}}};
    THEN("The fields of the json_objectt match the initialiser list.")
    {
      REQUIRE(object["number"].kind == jsont::kindt::J_NUMBER);
      REQUIRE(object["number"].value == "6");
      REQUIRE(object["string"].kind == jsont::kindt::J_STRING);
      REQUIRE(object["string"].value == "eggs");
      const json_objectt mice = to_json_object(object["mice"]);
      REQUIRE(mice["number"].kind == jsont::kindt::J_NUMBER);
      REQUIRE(mice["number"].value == "3");
      REQUIRE(mice["string"].kind == jsont::kindt::J_STRING);
      REQUIRE(mice["string"].value == "blind");
    }
  }
}

SCENARIO(
  "Test that json_objectt can be constructed using `ranget`",
  "[core][util][json]")
{
  GIVEN("A vector of numbers.")
  {
    const std::vector<int> input{1, 2, 3};
    THEN(
      "A json_objectt can be constructed from the vector of numbers using "
      "range and map.")
    {
      const json_objectt output =
        make_range(input)
          .map([](const int number) {
            const std::string number_as_string = std::to_string(number);
            return make_pair(number_as_string, json_stringt{number_as_string});
          })
          .collect<json_objectt>();
      REQUIRE(output["1"].kind == jsont::kindt::J_STRING);
      REQUIRE(output["1"].value == "1");
      REQUIRE(output["2"].kind == jsont::kindt::J_STRING);
      REQUIRE(output["2"].value == "2");
      REQUIRE(output["3"].kind == jsont::kindt::J_STRING);
      REQUIRE(output["3"].value == "3");
    };
  }
}

SCENARIO(
  "Test that source location pragmas are converted to JSON arrays.",
  "[core][util][json]")
{
  GIVEN("A source location with pragmas.")
  {
    source_locationt location;
    location.add_pragma("disable:pointer-check");
    location.add_pragma("disable:bounds-check");

    THEN("The pragmas are emitted as strings.")
    {
      const json_objectt output = json(location);
      const json_arrayt &pragmas = to_json_array(output["pragma"]);

      std::vector<std::string> pragma_values;
      for(const auto &pragma : pragmas)
      {
        REQUIRE(pragma.kind == jsont::kindt::J_STRING);
        pragma_values.push_back(pragma.value);
      }

      std::sort(pragma_values.begin(), pragma_values.end());
      REQUIRE(
        pragma_values ==
        std::vector<std::string>{
          "disable:bounds-check", "disable:pointer-check"});
    }
  }
}
