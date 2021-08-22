/*******************************************************************\

 Module: Tests for full_struct_abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <analyses/variable-sensitivity/full_struct_abstract_object/struct_builder.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "struct to predicate",
  "[core][analyses][variable-sensitivity][full_struct_abstract_object][to_"
  "predicate]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt environment(object_factory);
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("full_struct_abstract_object to predicate")
  {
    WHEN("it is TOP")
    {
      auto obj = build_top_struct();
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = build_bottom_struct();
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("{ .a = 1 }")
    {
      auto obj = build_struct({{"a", 1}}, environment, ns);
      THEN_PREDICATE(obj, "x.a == 1");
    }
    WHEN("{ .a = 1, .b = 2, .c = 3 }")
    {
      auto obj = build_struct({{"a", 1}, {"b", 2}, {"c", 3}}, environment, ns);
      THEN_PREDICATE(obj, "x.a == 1 && x.b == 2 && x.c == 3");
    }
    WHEN("{ .a = 1, .b = 2, .c = TOP }")
    {
      auto obj =
        build_struct({{"a", 1}, {"b", 2}, {"c", TOP_MEMBER}}, environment, ns);
      THEN_PREDICATE(obj, "x.a == 1 && x.b == 2");
    }
    WHEN("{ .a = TOP, .b = 2, .c = TOP }")
    {
      auto obj = build_struct(
        {{"a", TOP_MEMBER}, {"b", 2}, {"c", TOP_MEMBER}}, environment, ns);
      THEN_PREDICATE(obj, "x.b == 2");
    }
    WHEN("{ .a = TOP, .b = TOP, .c = TOP }")
    {
      auto obj = build_struct(
        {{"a", TOP_MEMBER}, {"b", TOP_MEMBER}, {"c", TOP_MEMBER}},
        environment,
        ns);
      THEN_PREDICATE(obj, "TRUE");
    }
  }
}
