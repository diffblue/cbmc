/*******************************************************************\

 Module: Unit tests for interval_abstract_valuet::meet

 Author: DiffBlue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

SCENARIO(
  "meet_interval_abstract_value",
  "[core][analyses][variable-sensitivity][interval_abstract_value][meet]")
{
  GIVEN("An environment with two intervals: 1--10 and 2--5")
  {
    const typet type = signedbv_typet(32);
    const exprt val1 = from_integer(1, type);
    REQUIRE(constant_interval_exprt::is_int(val1.type()));
    const exprt val10 = from_integer(10, type);
    const exprt val11 = from_integer(11, type);
    REQUIRE(constant_interval_exprt::is_int(val10.type()));
    const auto interval1_10 = constant_interval_exprt(val1, val10);

    const auto varx = symbol_exprt(type);
    const auto x_le_10 = binary_relation_exprt(varx, ID_le, val10);
    const auto lt_10_x = binary_relation_exprt(val10, ID_lt, varx);

    const exprt val2 = from_integer(2, type);
    const exprt val15 = from_integer(15, type);
    const auto interval2_15 = constant_interval_exprt(val2, val15);

    const auto interval1_2 = constant_interval_exprt(val1, val2);
    const auto interval10_15 = constant_interval_exprt(val10, val15);

    const auto temp_expr = unsignedbv_typet(32);
    const auto max_value = temp_expr.largest_expr();
    const auto x_ge_max = binary_relation_exprt(varx, ID_ge, max_value);
    const auto x_gt_max = binary_relation_exprt(varx, ID_gt, max_value);

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::intervals());

    abstract_environmentt enviroment{object_factory};
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN(
      "meeting constant AO with interval "
      "with a constant AO with the same interval")
    {
      abstract_object_pointert op1 = std::make_shared<interval_abstract_valuet>(
        interval1_10, enviroment, ns);
      abstract_object_pointert op2 = std::make_shared<interval_abstract_valuet>(
        interval1_10, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN("The original abstract object should be returned unchanged")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(cast_result->get_interval() == interval1_10);

        // Is optimal
        REQUIRE(result == op1);
      }
    }
    WHEN(
      "meeting constant AO with interval "
      "with a constant AO with the different interval")
    {
      abstract_object_pointert op1 =
        std::make_shared<interval_abstract_valuet>(interval1_2, enviroment, ns);
      abstract_object_pointert op2 = std::make_shared<interval_abstract_valuet>(
        interval10_15, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN("A new constant abstract object set to bottom should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE(cast_result->is_bottom());

        // Intersection should have this exact value
        REQUIRE_FALSE(result == op1);
      }
    }
    WHEN(
      "meeting constant AO with interval "
      "with a constant AO with the different interval")
    {
      abstract_object_pointert op1 = std::make_shared<interval_abstract_valuet>(
        interval1_10, enviroment, ns);
      abstract_object_pointert op2 = std::make_shared<interval_abstract_valuet>(
        interval2_15, enviroment, ns);

      const auto interval2_10 = constant_interval_exprt(val2, val10);
      abstract_object_pointert op3 = std::make_shared<interval_abstract_valuet>(
        interval2_10, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN("A new constant abstract object set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Intersection should have this exact value
        REQUIRE(cast_result->get_interval() == interval2_10);
      }
    }
    WHEN(
      "build constant AO with interval using le_expression "
      "then meet with a constant AO with the different interval")
    {
      abstract_object_pointert op1 =
        std::make_shared<interval_abstract_valuet>(x_le_10, enviroment, ns);
      abstract_object_pointert op2 = std::make_shared<interval_abstract_valuet>(
        interval2_15, enviroment, ns);

      const auto interval2_10 = constant_interval_exprt(val2, val10);
      abstract_object_pointert op3 = std::make_shared<interval_abstract_valuet>(
        interval2_10, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN(
        "A new constant abstract object set to intersection should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Intersection should have this exact value
        REQUIRE(cast_result->get_interval() == interval2_10);
      }
    }
    WHEN(
      "build constant AO with interval using lt_expression "
      "then meet with a constant AO with the different interval")
    {
      abstract_object_pointert op1 =
        std::make_shared<interval_abstract_valuet>(lt_10_x, enviroment, ns);
      abstract_object_pointert op2 = std::make_shared<interval_abstract_valuet>(
        interval2_15, enviroment, ns);

      const auto interval11_15 = constant_interval_exprt(val11, val15);
      abstract_object_pointert op3 = std::make_shared<interval_abstract_valuet>(
        interval11_15, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN(
        "A new constant abstract object set to intersection should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Intersection should have this exact value
        REQUIRE(cast_result->get_interval() == interval11_15);
      }
    }
    WHEN(
      "build constant AO with interval using ge_max_expression "
      "then meet with a constant AO with the different interval")
    {
      abstract_object_pointert op1 =
        std::make_shared<interval_abstract_valuet>(lt_10_x, enviroment, ns);
      abstract_object_pointert op2 =
        std::make_shared<interval_abstract_valuet>(x_ge_max, enviroment, ns);

      const auto intervalmax_max =
        constant_interval_exprt(max_value, max_exprt(max_value.type()));
      abstract_object_pointert op3 = std::make_shared<interval_abstract_valuet>(
        intervalmax_max, enviroment, ns);

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN(
        "A new constant abstract object set to intersection should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Intersection should have this exact value
        REQUIRE(cast_result->get_interval() == intervalmax_max);
      }
    }
    WHEN(
      "build constant AO with interval using gt_max_expression "
      "then meet with a constant AO with the different interval")
    {
      abstract_object_pointert op1 =
        std::make_shared<interval_abstract_valuet>(lt_10_x, enviroment, ns);
      abstract_object_pointert op2 =
        std::make_shared<interval_abstract_valuet>(x_gt_max, enviroment, ns);

      const auto &op2_cast =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(op2);
      REQUIRE(op2_cast->is_bottom());

      const auto interval10_max =
        constant_interval_exprt(val10, max_exprt(val10.type()));

      bool modified;
      abstract_object_pointert result =
        abstract_objectt::meet(op1, op2, modified);

      const auto &cast_result =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(result);

      THEN(
        "A new constant abstract object set to intersection should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of meet
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE(cast_result->is_bottom());
      }
    }
  }
}
