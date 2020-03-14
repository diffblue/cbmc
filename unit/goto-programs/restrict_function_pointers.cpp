/*******************************************************************\

Module: Restrict function pointers unit tests

Author: Daniel Poetzl

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/restrict_function_pointers.h>

#include <json/json_parser.h>

class fp_restrictionst : public function_pointer_restrictionst
{
  friend void restriction_parsing_test();
  friend void merge_restrictions_test();
};

void restriction_parsing_test()
{
  {
    const auto res =
      fp_restrictionst::parse_function_pointer_restriction("func1/func2");
    REQUIRE(res.first == "func1");
    REQUIRE(res.second.size() == 1);
    REQUIRE(res.second.find("func2") != res.second.end());
  }

  {
    const auto res =
      fp_restrictionst::parse_function_pointer_restriction("func1/func2,func3");
    REQUIRE(res.first == "func1");
    REQUIRE(res.second.size() == 2);
    REQUIRE(res.second.find("func2") != res.second.end());
    REQUIRE(res.second.find("func3") != res.second.end());
  }

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("func"),
    invalid_command_line_argument_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("/func"),
    invalid_command_line_argument_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("func/"),
    invalid_command_line_argument_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("func/,"),
    invalid_command_line_argument_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("func1/func2,"),
    invalid_command_line_argument_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction("func1/,func2"),
    invalid_command_line_argument_exceptiont);
}

void merge_restrictions_test()
{
  fp_restrictionst::restrictionst r1;
  r1.emplace("fp1", std::unordered_set<irep_idt>{"func1", "func2"});
  r1.emplace("fp2", std::unordered_set<irep_idt>{"func1"});

  fp_restrictionst::restrictionst r2;
  r2.emplace("fp1", std::unordered_set<irep_idt>{"func1", "func3"});

  fp_restrictionst::restrictionst result =
    fp_restrictionst::merge_function_pointer_restrictions(r1, r2);

  REQUIRE(result.size() == 2);

  const auto &fp1_restrictions = result.at("fp1");
  REQUIRE(fp1_restrictions.size() == 3);
  REQUIRE(fp1_restrictions.count("func1") == 1);
  REQUIRE(fp1_restrictions.count("func2") == 1);
  REQUIRE(fp1_restrictions.count("func3") == 1);

  const auto &fp2_restrictions = result.at("fp2");
  REQUIRE(fp2_restrictions.size() == 1);
  REQUIRE(fp2_restrictions.count("func1") == 1);
}

TEST_CASE("Restriction parsing", "[core]")
{
  restriction_parsing_test();
}

TEST_CASE("Merge function pointer restrictions", "[core]")
{
  merge_restrictions_test();
}

TEST_CASE("Json conversion", "[core]")
{
  // conversion json1 -> restrictions1 -> json2 -> restrictions2
  // then check that restrictions1 == restrictions2
  //
  // we use json as a starting point as it is easy to write, and we compare the
  // restrictions as it is a canonical representation (in contrast, the json
  // representation for the same restrictions can differ, due to the array
  // elements appearing in different orders)

  std::istringstream ss(
    "{"
    "  \"use_f.function_pointer_call.1\": [\"f\", \"g\"],"
    "  \"use_f.function_pointer_call.2\": [\"h\"]"
    "}");

  jsont json1;

  parse_json(ss, "", null_message_handler, json1);

  // json1 -> restrictions1
  const auto function_pointer_restrictions1 =
    function_pointer_restrictionst::from_json(json1);

  const auto &restrictions = function_pointer_restrictions1.restrictions;

  REQUIRE(restrictions.size() == 2);

  const auto &fp1_restrictions =
    restrictions.at("use_f.function_pointer_call.1");
  REQUIRE(fp1_restrictions.size() == 2);
  REQUIRE(fp1_restrictions.count("f") == 1);
  REQUIRE(fp1_restrictions.count("g") == 1);

  const auto &fp2_restrictions =
    restrictions.at("use_f.function_pointer_call.2");
  REQUIRE(fp2_restrictions.size() == 1);
  REQUIRE(fp2_restrictions.count("h") == 1);

  // restrictions1 -> json2
  const auto json2 = function_pointer_restrictions1.to_json();

  // json2 -> restrictions2
  const auto function_pointer_restrictions2 =
    function_pointer_restrictionst::from_json(json2);

  REQUIRE(
    function_pointer_restrictions1.restrictions ==
    function_pointer_restrictions2.restrictions);
}
