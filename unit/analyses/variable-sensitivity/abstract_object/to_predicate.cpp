/*******************************************************************\

 Module: Tests for abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>
#include <util/mathematical_types.h>

SCENARIO(
  "constant  to predicate",
  "[core][analyses][variable-sensitivity][abstract_object][to_predicate]")
{
  GIVEN("an abstract object")
  {
    WHEN("it is TOP")
    {
      auto obj = make_top_object();
      auto pred = obj->to_predicate(nil_exprt());
      THEN("predicate is true")
      {
        REQUIRE(pred == true_exprt());
      }
    }
    WHEN("it is BOTTOM")
    {
      auto obj = make_bottom_object();
      auto pred = obj->to_predicate(nil_exprt());
      THEN("predicate is false")
      {
        REQUIRE(pred == false_exprt());
      }
    }
    WHEN("it is neither TOP nor BOTTOM")
    {
      auto obj =
        std::make_shared<abstract_objectt>(integer_typet(), false, false);
      auto pred = obj->to_predicate(nil_exprt());
      THEN("predicate is nil")
      {
        REQUIRE(pred == nil_exprt());
      }
    }
  }
}
