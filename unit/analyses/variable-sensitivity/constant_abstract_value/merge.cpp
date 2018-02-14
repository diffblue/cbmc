/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <typeinfo>
#include <testing-utils/catch.hpp>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <util/arith_tools.h>
#include <util/c_types.h>


SCENARIO("merge_constant_abstract_value",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  GIVEN("An environment with two values: 1 and 2")
  {
    const exprt val1=from_integer(1, integer_typet());
    const exprt val2=from_integer(2, integer_typet());

    abstract_environmentt enviroment;
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("merging constant AO with value "
      "with a constant AO with the same value")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);

      THEN("The original abstract object should be returned unchanged")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(cast_result->to_constant()==val1);

            // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("merging constant AO with value "
      "with a constant AO with the different value")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val2, enviroment, ns);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);

      THEN("A new constant abstract object set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // We currently don't require the value has any reasonable value

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
        }
    }
    WHEN("merging constant AO with value with a constant AO set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);

      THEN("A new AO of the same type set to top ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // We currently don't require the value has any reasonable value

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
      }
    }
    WHEN("merging constant AO with value with a constant AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);

      THEN("The original AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(cast_result->to_constant()==val1);

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("merging constant AO set to top with a constant AO with a value")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("WE should return the same value")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging constant AO set to top with a constant AO set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("WE should return the same value")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging constant AO set to top with a constant AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
      abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("WE should return the same value")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging constant AO set to bottom with a constant AO with a value")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("We should get an abstract object that has the same value as op2")
      {
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
        REQUIRE(result->to_constant()==val1);
      }
    }
    WHEN("merging constant AO set to bottom with a constant AO set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("We should get a top abstract object back")
      {
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
      }
    }
    WHEN("merging constant AO set to bottom with a constant AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("We should get the same (bottom) AO back")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        // Optimization correctness
        REQUIRE(result==op1);
      }
    }
    WHEN("merging constant AO with value with a abstract object set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);

      THEN("We should get a new AO of the same type but set to top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // We currently don't require the value has any reasonable value

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
      }
    }
    WHEN("merging constant AO with value with a abstract object set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
      THEN("We should get the same constant AO back")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(cast_result->to_constant()==val1);

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("merging constant AO set to top with a abstract object set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("We should get the same abstract object back")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("merging constant AO set to top with a abstract object set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("Should get the same abstract object back")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("merging constant AO set to bottom with a abstract object set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("Return a new top abstract object of the same type")
      {
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // We don't optimize for returning the second parameter if we can

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("merging constant AO set to bottom with a AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("Return the original abstract object")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        // Optimization check
        REQUIRE(result==op1);

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("merging AO set to top with a constant AO with a value")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      bool modified;

      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging AO set to top with a constant AO set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging AO set to top with a constant AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    WHEN("merging AO set to bottom with a constant AO with a value")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("The a new top AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(typeid(result.get())==typeid(const abstract_objectt *));
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
      }

      // We don't optimize for returning the second parameter if we can
    }
    WHEN("merging AO set to bottom with a constant AO set to top")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("The a new top AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // We don't optimize for returning the second parameter if we can
      }
    }
    WHEN("merging AO set to bottom with a constant AO set to bottom")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      abstract_object_pointert op2=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        REQUIRE(result==op1);
      }
    }
  }
}
