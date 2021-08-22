/*******************************************************************\

 Module: Tests for full_array_abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <analyses/variable-sensitivity/full_array_abstract_object/array_builder.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/symbol_table.h>

SCENARIO(
  "array to predicate",
  "[core][analyses][variable-sensitivity][full_array_abstract_object][to_"
  "predicate]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt environment(object_factory);
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("full_array_abstract_object to predicate")
  {
    WHEN("it is TOP")
    {
      auto obj = build_top_array();
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = build_bottom_array();
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("[ 1 ]")
    {
      auto obj = build_array({1}, environment, ns);
      THEN_PREDICATE(obj, "x[0] == 1");
    }
    WHEN("[ 1, 2, 3 ]")
    {
      auto obj = build_array({1, 2, 3}, environment, ns);
      THEN_PREDICATE(obj, "x[0] == 1 && x[1] == 2 && x[2] == 3");
    }
    WHEN("[ 1, 2, TOP ]")
    {
      auto obj = build_array({1, 2, TOP_MEMBER}, environment, ns);
      THEN_PREDICATE(obj, "x[0] == 1 && x[1] == 2");
    }
    WHEN("[ TOP, 2, TOP ]")
    {
      auto obj = build_array({TOP_MEMBER, 2, TOP_MEMBER}, environment, ns);
      THEN_PREDICATE(obj, "x[1] == 2");
    }
    WHEN("[ TOP, TOP, TOP ]")
    {
      auto obj =
        build_array({TOP_MEMBER, TOP_MEMBER, TOP_MEMBER}, environment, ns);
      THEN_PREDICATE(obj, "TRUE");
    }
  }
}
