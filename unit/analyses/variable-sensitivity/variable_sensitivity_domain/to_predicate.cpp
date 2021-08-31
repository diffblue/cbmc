/*******************************************************************\

 Module: Tests for variable_sensitivity_domaint::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "variable_sensitivity_domain to predicate",
  "[core][analyses][variable-sensitivity][variable_sensitivity_domain][to_"
  "predicate]")
{
  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("to_predicate()")
  {
    WHEN("it is TOP")
    {
      auto domain = variable_sensitivity_domaint(object_factory, config);
      domain.make_top();
      THEN_PREDICATE(domain, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto domain = variable_sensitivity_domaint(object_factory, config);
      domain.make_bottom();
      THEN_PREDICATE(domain, "FALSE");
    }
  }
  GIVEN("to_predicate(expr)")
  {
    WHEN("1 + 2")
    {
      auto type = signedbv_typet(32);
      auto val1 = from_integer(1, type);
      auto val2 = from_integer(2, type);

      auto domain = variable_sensitivity_domaint(object_factory, config);
      domain.make_top();

      auto pred = domain.to_predicate(plus_exprt(val1, val2), ns);
      THEN("predicate is 1 + 2 == 3")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "1 + 2 == 3");
      }
    }
  }
  GIVEN("to_predicate(std::vector<expr>)")
  {
    auto domain = variable_sensitivity_domaint(object_factory, config);
    domain.make_top();

    auto type = signedbv_typet(32);
    auto val1 = from_integer(1, type);
    auto val2 = from_integer(2, type);
    auto val3 = from_integer(3, type);
    auto onePlusTwo = plus_exprt(val1, val2);
    auto twoPlusThree = plus_exprt(val2, val3);

    WHEN("{ }")
    {
      auto pred = domain.to_predicate(std::vector<exprt>(), ns);
      THEN("predicate is FALSE")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "FALSE");
      }
    }
    WHEN("{ 1 + 2 }")
    {
      auto pred = domain.to_predicate({onePlusTwo}, ns);
      THEN("predicate is 1 + 2 == 3")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "1 + 2 == 3");
      }
    }

    WHEN("{ 1 + 2, 2 + 3 }")
    {
      auto pred = domain.to_predicate({onePlusTwo, twoPlusThree}, ns);
      THEN("predicate is 1 + 2 == 3 && 2 + 3 == 5")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "1 + 2 == 3 && 2 + 3 == 5");
      }
    }
  }
}
