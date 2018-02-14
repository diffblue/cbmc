/*******************************************************************\

 Module: Unit tests for variable/sensitivity/abstract_object::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <analyses/variable-sensitivity/abstract_object.h>
#include <util/std_types.h>

SCENARIO("merge_abstract_object",
  "[core][analyses][variable-sensitivity][abstract_object][merge]")
{
  GIVEN("Two abstract objects of type pointer")
  {
    const typet object_type=signedbv_typet(32);
    WHEN("Both are top")
    {
      abstract_object_pointert op1=
        std::make_shared<const abstract_objectt>(object_type, true, false);

      abstract_object_pointert op2=
        std::make_shared<const abstract_objectt>(object_type, true, false);

      bool modifications;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modifications);

      THEN("The result is the original abstract object")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("The first is top, the second is bottom")
    {
      abstract_object_pointert op1=
      std::make_shared<const abstract_objectt>(object_type, true, false);

      abstract_object_pointert op2=
      std::make_shared<const abstract_objectt>(object_type, false, true);

      bool modifications;
      abstract_object_pointert result=
          abstract_objectt::merge(op1, op2, modifications);

      THEN("The result is the original abstract object")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("The first is bottom and the second is top")
    {
      abstract_object_pointert op1=
      std::make_shared<const abstract_objectt>(object_type, false, true);
      abstract_object_pointert op2=
      std::make_shared<const abstract_objectt>(object_type, true, false);

      bool modifications;
      abstract_object_pointert result=
      abstract_objectt::merge(op1, op2, modifications);

      THEN("The result is top and a new abstract object")
      {
        // Simple correctness of merge
        REQUIRE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        REQUIRE_FALSE(op1==result);
      }
    }
    WHEN("Both are bottom")
    {
      abstract_object_pointert op1=
      std::make_shared<const abstract_objectt>(object_type, false, true);
      abstract_object_pointert op2=
      std::make_shared<const abstract_objectt>(object_type, false, true);

      bool modifications;
      abstract_object_pointert result=
      abstract_objectt::merge(op1, op2, modifications);

      THEN("The result is the original abstract object")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modifications);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
  }
}
