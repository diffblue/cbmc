/*******************************************************************\

 Module: Unit tests for constant_array_abstract_object::merge

 Author: DiffBlue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <typeinfo>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/full_array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

typedef full_array_abstract_objectt::full_array_pointert
  full_array_abstract_object_pointert;

// Util

class array_utilt
{
public:
  array_utilt(const abstract_environmentt &enviroment, const namespacet &ns)
    : enviroment(enviroment), ns(ns)
  {
  }

  full_array_abstract_objectt::full_array_pointert
  build_array(const exprt &array_expr)
  {
    return std::make_shared<full_array_abstract_objectt>(
      array_expr, enviroment, ns);
  }

  full_array_abstract_objectt::full_array_pointert
  build_top_array(const typet &array_type)
  {
    return std::make_shared<full_array_abstract_objectt>(
      array_type, true, false);
  }

  full_array_abstract_objectt::full_array_pointert
  build_bottom_array(const typet &array_type)
  {
    return std::make_shared<full_array_abstract_objectt>(
      array_type, false, true);
  }

  exprt read_index(
    full_array_abstract_object_pointert array_object,
    const index_exprt &index) const
  {
    return array_object->expression_transform(index, {}, enviroment, ns)
      ->to_constant();
  }

private:
  const abstract_environmentt &enviroment;
  const namespacet ns;
};

SCENARIO(
  "merge_constant_array_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][constant_array_abstract_object][merge]")
{
  GIVEN("Two arrays of size 3, whose first elements are the same")
  {
    const array_typet array_type(
      integer_typet(), from_integer(3, integer_typet()));

    // int val1[3] = {1, 2, 3}
    exprt::operandst val1_op;
    val1_op.push_back(from_integer(1, integer_typet()));
    val1_op.push_back(from_integer(2, integer_typet()));
    val1_op.push_back(from_integer(3, integer_typet()));
    exprt val1 = array_exprt(val1_op, array_type);

    // int val2[3] = {1, 4, 5}
    exprt::operandst val2_op;
    val2_op.push_back(from_integer(1, integer_typet()));
    val2_op.push_back(from_integer(4, integer_typet()));
    val2_op.push_back(from_integer(5, integer_typet()));
    exprt val2 = array_exprt(val2_op, array_type);

    // index_exprt for reading from an array
    const index_exprt i0 =
      index_exprt(nil_exprt(), from_integer(0, integer_typet()));
    const index_exprt i1 =
      index_exprt(nil_exprt(), from_integer(1, integer_typet()));
    const index_exprt i2 =
      index_exprt(nil_exprt(), from_integer(2, integer_typet()));

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::constant_domain());
    abstract_environmentt enviroment(object_factory);
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    array_utilt util(enviroment, ns);

    WHEN("Merging two constant array AOs with the same array")
    {
      auto op1 = util.build_array(val1);
      auto op2 = util.build_array(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == val1.operands()[0]);
        REQUIRE(util.read_index(cast_result, i1) == val1.operands()[1]);
        REQUIRE(util.read_index(cast_result, i2) == val1.operands()[2]);

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN("Merging two constant array AOs with different value arrays")
    {
      auto op1 = util.build_array(val1);
      auto op2 = util.build_array(val2);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);

      THEN(
        "A new constant array AO whose first value is the same and "
        "the other two are top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == val1.operands()[0]);
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant array AO with a value "
      "with a constant array AO set to top")
    {
      auto op1 = util.build_array(val1);
      auto op2 = util.build_top_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("A new constant array AO set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // We can't reuse the abstract object as the value has changed
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant array AO with a value "
      "with a constant array AO set to bottom")
    {
      auto op1 = util.build_array(val1);
      auto op2 = util.build_bottom_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original const AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == val1.operands()[0]);
        REQUIRE(util.read_index(cast_result, i1) == val1.operands()[1]);
        REQUIRE(util.read_index(cast_result, i2) == val1.operands()[2]);

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to top "
      "with a constant array AO with a value")
    {
      auto op1 = util.build_top_array(array_type);
      auto op2 = util.build_array(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to top "
      "with a constant array AO set to top")
    {
      auto op1 = util.build_top_array(array_type);
      auto op2 = util.build_top_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to top "
      "with a constant array AO set to bottom")
    {
      auto op1 = util.build_top_array(array_type);
      auto op2 = util.build_bottom_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to bottom "
      "with a constant array AO with a value")
    {
      auto op1 = util.build_bottom_array(array_type);
      auto op2 = util.build_array(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("A new AO should be returned with op2s valuee")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == val1.operands()[0]);
        REQUIRE(util.read_index(cast_result, i1) == val1.operands()[1]);
        REQUIRE(util.read_index(cast_result, i2) == val1.operands()[2]);

        // Is optimal
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to bottom "
      "with a constant array AO set to top")
    {
      auto op1 = util.build_bottom_array(array_type);
      auto op2 = util.build_top_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("A new constant array AO should be returned set to top ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i1) == nil_exprt());
        REQUIRE(util.read_index(cast_result, i2) == nil_exprt());

        // Is optimal
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant array AO set to bottom "
      "with a constant array AO set to bottom")
    {
      auto op1 = util.build_bottom_array(array_type);
      auto op2 = util.build_bottom_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("The original bottom AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE(cast_result->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant array AO with value "
      "with a abstract object set to top")
    {
      const auto &op1 = util.build_array(val1);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);

      THEN("We should get a new AO of the same type but set to top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant array AO with value "
      "with a abstract object set to bottom")
    {
      const auto &op1 = util.build_array(val1);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_array_abstract_objectt>(
          result.object);
      THEN("We should get the same constant array AO back")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0) == val1.operands()[0]);
        REQUIRE(util.read_index(cast_result, i1) == val1.operands()[1]);
        REQUIRE(util.read_index(cast_result, i2) == val1.operands()[2]);

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant array AO set to top "
      "with a abstract object set to top")
    {
      const auto &op1 = util.build_top_array(array_type);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("We should get the same abstract object back")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);

        // Is type still correct
        const auto &cast_result =
          std::dynamic_pointer_cast<const full_array_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN(
      "Merging constant array AO set to top "
      "with a abstract object set to bottom")
    {
      const auto &op1 = util.build_top_array(array_type);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("Should get the same abstract object back")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);

        // Is type still correct
        const auto &cast_result =
          std::dynamic_pointer_cast<const full_array_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN(
      "Merging constant array AO set to bottom "
      " with a abstract object set to top")
    {
      const auto &op1 = util.build_bottom_array(array_type);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("Return a new top abstract object of the same type")
      {
        // Simple correctness of merge
        REQUIRE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // We don't optimize for returning the second parameter if we can

        // Is type still correct
        const auto &cast_result =
          std::dynamic_pointer_cast<const full_array_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant array AO set to bottom with a AO set to bottom")
    {
      const auto &op1 = util.build_bottom_array(array_type);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("Return the original abstract object")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(result.object->is_top());
        REQUIRE(result.object->is_bottom());

        // Optimization check
        REQUIRE(result.object == op1);

        // Is type still correct
        const auto &cast_result =
          std::dynamic_pointer_cast<const full_array_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging AO set to top with a constant array AO with a value")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_array(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN("Merging AO set to top with a constant array AO set to top")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_top_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN("Merging AO set to top with a constant array AO set to bottom")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_bottom_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // Is optimal
        REQUIRE(result.object == op1);
      }
    }
    WHEN("Merging AO set to bottom with a constant array AO with a value")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_array(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("The a new top AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE(result.modified);
        REQUIRE(
          typeid(result.object.get()) == typeid(const abstract_objectt *));
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());
      }

      // We don't optimize for returning the second parameter if we can
    }
    WHEN("Merging AO set to bottom with a constant array AO set to top")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_top_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("The a new top AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // We don't optimize for returning the second parameter if we can
      }
    }
    WHEN("Merging AO set to bottom with a constant array AO set to bottom")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_bottom_array(array_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(result.object->is_top());
        REQUIRE(result.object->is_bottom());

        REQUIRE(result.object == op1);
      }
    }
  }
}
