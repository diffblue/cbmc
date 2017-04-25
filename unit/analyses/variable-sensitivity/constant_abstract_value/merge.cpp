/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <typeinfo>
#include <catch.hpp>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>


// Debug printer for irept
std::ostream &operator<<(std::ostream &os, const irept &value)
{
        os << value.pretty();
        return os;
}

TEST_CASE("merge_constant_abstract_value",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const exprt val1=constant_exprt::integer_constant(1);
  const exprt val2=constant_exprt::integer_constant(2);

  abstract_environmentt enviroment;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  abstract_object_pointert result;
  bool modified;

  abstract_object_pointert op1;
  abstract_object_pointert op2;
  SECTION("constant AO merge with constant AO")
  {
    SECTION("merge value with...")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      SECTION("same value")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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
      SECTION("different value")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val2, enviroment, ns);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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
    SECTION("merge top with")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      abstract_object_pointert op2;
      SECTION("value")
      {
        op2=std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      }
      SECTION("top")
      {
        op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
      }
      SECTION("bottom")
      {
        op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
      }

      // Whatever we are merging with, we should stay top

      result=abstract_objectt::merge(op1, op2, modified);
      // Simple correctness of merge
      REQUIRE_FALSE(modified);
      REQUIRE(result->is_top());
      REQUIRE_FALSE(result->is_bottom());

      // Is optimal
      REQUIRE(op1==result);
    }
    SECTION("merge bottom with")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      abstract_object_pointert op2;

      SECTION("value")
      {
        op2=
          std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);
        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
        REQUIRE(result->to_constant()==val1);

      }
      SECTION("top")
      {
        op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), true, false);
        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
      }
      SECTION("bottom")
      {
        op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);
        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        // Optimization correctness
        REQUIRE(result==op1);
      }

      // Whatever we are merging with, we should end up as them



      // We don't optimize for returning the second parameter if we can
    }
  }
  SECTION("constant AO merge with AO")
  {
    SECTION("merge value with...")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), true, false);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), false, true);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
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
    SECTION("merge top with")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), true, false);

        // Whatever we are merging with, we should stay top

        result=abstract_objectt::merge(op1, op2, modified);
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
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), false, true);

        // Whatever we are merging with, we should stay top

        result=abstract_objectt::merge(op1, op2, modified);
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
    SECTION("merge bottom with")
    {
      abstract_object_pointert op1=
        std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), true, false);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top()==op2->is_top());
        REQUIRE(result->is_bottom()==op2->is_bottom());

        // We don't optimize for returning the second parameter if we can

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<abstract_objectt>(val1.type(), false, true);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        // We don't optimize for returning the second parameter if we can

        // Is type still correct
        const auto &cast_result=
          std::dynamic_pointer_cast<const constant_abstract_valuet>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
  }
  SECTION("AO merge with constant AO")
  {
    SECTION("merge top with")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      SECTION("value")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // Is optimal
        REQUIRE(op1==result);
      }
    }
    SECTION("merge bottom with")
    {
      abstract_object_pointert op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      SECTION("value")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1, enviroment, ns);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(typeid(result.get())==typeid(const abstract_objectt *));
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // We don't optimize for returning the second parameter if we can
      }
      SECTION("top")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), true, false);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE(modified);
        REQUIRE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());

        // We don't optimize for returning the second parameter if we can
      }
      SECTION("bottom")
      {
        abstract_object_pointert op2=
          std::make_shared<constant_abstract_valuet>(val1.type(), false, true);

        result=abstract_objectt::merge(op1, op2, modified);
        // Simple correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(result->is_top());
        REQUIRE(result->is_bottom());

        REQUIRE(result==op1);
      }
    }
  }
}
