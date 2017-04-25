/*******************************************************************\

 Module: Unit tests for variable/sensitivity/abstract_object::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <analyses/variable-sensitivity/abstract_object.h>
#include <util/std_types.h>

TEST_CASE("merge_abstract_object",
  "[core][analyses][variable-sensitivity][abstract_object][merge]")
{
  SECTION("abstract object merge with abstract object")
  {
    const typet object_type=signedbv_typet(32);
    SECTION("merging top with...")
    {
      abstract_object_pointert op1=
        std::make_shared<const abstract_objectt>(object_type, true, false);

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<const abstract_objectt>(object_type, true, false);

        bool modifications;
        abstract_object_pointert result=
          abstract_objectt::merge(op1, op2, modifications);

        // Simple correctness of merge
        REQUIRE_FALSE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<const abstract_objectt>(object_type, false, true);

        bool modifications;
        abstract_object_pointert result=
          abstract_objectt::merge(op1, op2, modifications);

        // Simple correctness of merge
        REQUIRE_FALSE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    SECTION("merging bottom with...")
    {
      abstract_object_pointert op1=
        std::make_shared<const abstract_objectt>(object_type, false, true);

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<const abstract_objectt>(object_type, true, false);

        bool modifications;
        abstract_object_pointert result=
          abstract_objectt::merge(op1, op2, modifications);

        // Simple correctness of merge
        REQUIRE(modifications);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
      }
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<const abstract_objectt>(object_type, false, true);

        bool modifications;
        abstract_object_pointert result=
          abstract_objectt::merge(op1, op2, modifications);

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
