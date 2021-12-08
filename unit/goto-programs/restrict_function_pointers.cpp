/*******************************************************************\

Module: Restrict function pointers unit tests

Author: Daniel Poetzl

\*******************************************************************/

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/label_function_pointer_call_sites.h>
#include <goto-programs/restrict_function_pointers.h>

#include <json/json_parser.h>

class fp_restrictionst : public function_pointer_restrictionst
{
  friend void restriction_parsing_test();
  friend void merge_restrictions_test();
  friend void get_function_pointer_by_name_restrictions_test();
};

void restriction_parsing_test()
{
  goto_modelt goto_model;

  {
    const auto res = fp_restrictionst::parse_function_pointer_restriction(
      "func1/func2", "test", goto_model);
    REQUIRE(res.first == "func1");
    REQUIRE(res.second.size() == 1);
    REQUIRE(res.second.find("func2") != res.second.end());
  }

  {
    const auto res = fp_restrictionst::parse_function_pointer_restriction(
      "func1/func2,func3", "test", goto_model);
    REQUIRE(res.first == "func1");
    REQUIRE(res.second.size() == 2);
    REQUIRE(res.second.find("func2") != res.second.end());
    REQUIRE(res.second.find("func3") != res.second.end());
  }

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "func", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "/func", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "func/", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "func/,", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "func1/func2,", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);

  REQUIRE_THROWS_AS(
    fp_restrictionst::parse_function_pointer_restriction(
      "func1/,func2", "test", goto_model),
    fp_restrictionst::invalid_restriction_exceptiont);
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

void get_function_pointer_by_name_restrictions_test()
{
  SECTION("Translate parameter restriction to indexed restriction")
  {
    const std::string code = R"(
      typedef void (*fp_t)(void);
      void f();

      void func(fp_t fp)
      {
        f(); // ignored

        fp();
      }

      void main() {}
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    label_function_pointer_call_sites(goto_model);

    const auto restrictions =
      fp_restrictionst::get_function_pointer_by_name_restrictions(
        {"func::fp/g"}, goto_model);

    REQUIRE(restrictions.size() == 1);

    const auto set = restrictions.at("func.function_pointer_call.1");
    REQUIRE(set.size() == 1);
    REQUIRE(set.count("g") == 1);
  }

  SECTION("Translate local nested variable restriction to indexed restriction")
  {
    const std::string code = R"(
      typedef void (*fp_t)(void);
      void f();

      void main()
      {
        f(); // ignored

        {
          fp_t fp;
          fp();
        }
      }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    label_function_pointer_call_sites(goto_model);

    const auto restrictions =
      fp_restrictionst::get_function_pointer_by_name_restrictions(
        {"main::1::1::fp/g"}, goto_model);

    REQUIRE(restrictions.size() == 1);

    const auto set = restrictions.at("main.function_pointer_call.1");
    REQUIRE(set.size() == 1);
    REQUIRE(set.count("g") == 1);
  }

  SECTION("Translate global variable restriction to indexed restriction")
  {
    const std::string code = R"(
      typedef void (*fp_t)(void);
      void f();

      fp_t fp;

      void main()
      {
        f(); // ignored

        fp();
      }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    label_function_pointer_call_sites(goto_model);

    const auto restrictions =
      fp_restrictionst::get_function_pointer_by_name_restrictions(
        {"fp/g"}, goto_model);

    REQUIRE(restrictions.size() == 1);

    const auto set = restrictions.at("main.function_pointer_call.1");
    REQUIRE(set.size() == 1);
    REQUIRE(set.count("g") == 1);
  }

  SECTION(
    "Translate a variable restriction to indexed restrictions, "
    "for the case when a function pointer is called more than once")
  {
    const std::string code = R"(
      typedef void (*fp_t)(void);
      void f();

      fp_t fp;

      void main()
      {
        f(); // ignored

        fp();
        fp(); // second call to same function pointer
      }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    label_function_pointer_call_sites(goto_model);

    const auto restrictions =
      fp_restrictionst::get_function_pointer_by_name_restrictions(
        {"fp/g"}, goto_model);

    REQUIRE(restrictions.size() == 2);

    const auto set1 = restrictions.at("main.function_pointer_call.1");
    REQUIRE(set1.size() == 1);
    REQUIRE(set1.count("g") == 1);

    const auto set2 = restrictions.at("main.function_pointer_call.2");
    REQUIRE(set2.size() == 1);
    REQUIRE(set2.count("g") == 1);
  }
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

TEST_CASE(
  "Get function pointer by name restrictions",
  "[core][goto-programs][restrict-function-pointers]")
{
  get_function_pointer_by_name_restrictions_test();
}
