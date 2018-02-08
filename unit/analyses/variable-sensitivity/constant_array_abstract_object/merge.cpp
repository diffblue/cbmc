/*******************************************************************\

 Module: Unit tests for constant_array_abstract_object::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <typeinfo>
#include <catch.hpp>
#include <util/namespace.h>
#include <util/options.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

typedef constant_array_abstract_objectt::constant_array_pointert
  constant_array_abstract_object_pointert;

// Util


class array_utilt
{
public:
  array_utilt(const abstract_environmentt &enviroment, const namespacet &ns):
    enviroment(enviroment), ns(ns)
  {}

  constant_array_abstract_objectt::constant_array_pointert build_array(
    const exprt &array_expr)
  {
    return std::make_shared<constant_array_abstract_objectt>(
      array_expr, enviroment, ns);
  }

  constant_array_abstract_objectt::constant_array_pointert build_top_array(
    const typet &array_type)
  {
    return std::make_shared<constant_array_abstract_objectt>(
      array_type, true, false);
  }

  constant_array_abstract_objectt::constant_array_pointert build_bottom_array(
    const typet &array_type)
  {
    return std::make_shared<constant_array_abstract_objectt>(
      array_type, false, true);
  }

  exprt read_index(
     constant_array_abstract_object_pointert array_object,
    const index_exprt &index) const
  {
    return array_object->read(enviroment, index, ns)->to_constant();
  }

private:
  const abstract_environmentt &enviroment;
  const namespacet ns;
};

SCENARIO("merge_constant_array_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][constant_array_abstract_object][merge]")
{
  GIVEN("Two arrays of size 3, whose first elements are the same")
  {
    const array_typet array_type(
      integer_typet(), constant_exprt::integer_constant(3));

    // int val1[3] = {1, 2, 3}
    exprt val1=array_exprt(array_type);
    val1.operands().push_back(constant_exprt::integer_constant(1));
    val1.operands().push_back(constant_exprt::integer_constant(2));
    val1.operands().push_back(constant_exprt::integer_constant(3));

    // int val2[3] = {1, 4, 5}
    exprt val2=array_exprt(array_type);
    val2.operands().push_back(constant_exprt::integer_constant(1));
    val2.operands().push_back(constant_exprt::integer_constant(4));
    val2.operands().push_back(constant_exprt::integer_constant(5));

    // index_exprt for reading from an array
    const index_exprt i0=
      index_exprt(nil_exprt(), constant_exprt::integer_constant(0));
    const index_exprt i1=
      index_exprt(nil_exprt(), constant_exprt::integer_constant(1));
    const index_exprt i2=
      index_exprt(nil_exprt(), constant_exprt::integer_constant(2));

    abstract_environmentt enviroment;
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    optionst options;
    options.set_option("pointers", true);
    options.set_option("arrays", true);
    options.set_option("structs", true);
    variable_sensitivity_object_factoryt::instance().set_options(options);

    array_utilt util(enviroment, ns);

    abstract_object_pointert result;
    bool modified=false;

    WHEN("Merging two constant array AOs with the same array")
    {
      auto op1=util.build_array(val1);
      auto op2=util.build_array(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==val1.op0());
        REQUIRE(util.read_index(cast_result, i1)==val1.op1());
        REQUIRE(util.read_index(cast_result, i2)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging two constant array AOs with different value arrays")
    {
      auto op1=util.build_array(val1);
      auto op2=util.build_array(val2);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);

      THEN("A new constant array AO whose first value is the same and "
        "the other two are top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==val1.op0());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
      }
    }
    WHEN("Merging a constant array AO with a value "
      "with a constant array AO set to top")
    {
      auto op1=util.build_array(val1);
      auto op2=util.build_top_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("A new constant array AO set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // We can't reuse the abstract object as the value has changed
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant array AO with a value "
      "with a constant array AO set to bottom")
    {
      auto op1=util.build_array(val1);
      auto op2=util.build_bottom_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original const AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==val1.op0());
        REQUIRE(util.read_index(cast_result, i1)==val1.op1());
        REQUIRE(util.read_index(cast_result, i2)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant array AO set to top "
      "with a constant array AO with a value")
    {
      auto op1=util.build_top_array(array_type);
      auto op2=util.build_array(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant array AO set to top "
      "with a constant array AO set to top")
    {
      auto op1=util.build_top_array(array_type);
      auto op2=util.build_top_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant array AO set to top "
      "with a constant array AO set to bottom")
    {
      auto op1=util.build_top_array(array_type);
      auto op2=util.build_bottom_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original constant array AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant array AO set to bottom "
      "with a constant array AO with a value")
    {
      auto op1=util.build_bottom_array(array_type);
      auto op2=util.build_array(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("A new AO should be returned with op2s valuee")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==val1.op0());
        REQUIRE(util.read_index(cast_result, i1)==val1.op1());
        REQUIRE(util.read_index(cast_result, i2)==val1.op2());

        // Is optimal
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant array AO set to bottom "
      "with a constant array AO set to top")
    {
      auto op1=util.build_bottom_array(array_type);
      auto op2=util.build_top_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("A new constant array AO should be returned set to top ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
        REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

        // Is optimal
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant array AO set to bottom "
      "with a constant array AO set to bottom")
    {
      auto op1=util.build_bottom_array(array_type);
      auto op2=util.build_bottom_array(array_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("The original bottom AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE(cast_result->is_bottom());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging constant array AO with value "
      "with a abstract object set to top")
    {
      const auto &op1=util.build_array(val1);
      const auto &op2=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);

      THEN("We should get a new AO of the same type but set to top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
      }
    }
    WHEN("Merging constant array AO with value "
      "with a abstract object set to bottom")
    {
      const auto &op1=util.build_array(val1);
      const auto &op2=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
          result);
      THEN("We should get the same constant array AO back")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_index(cast_result, i0)==val1.op0());
        REQUIRE(util.read_index(cast_result, i1)==val1.op1());
        REQUIRE(util.read_index(cast_result, i2)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging constant array AO set to top "
      "with a abstract object set to top")
    {
      const auto &op1=
        util.build_top_array(array_type);
      const auto &op2=
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
          std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
            result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant array AO set to top "
      "with a abstract object set to bottom")
    {
      const auto &op1=
        util.build_top_array(array_type);
      const auto &op2=
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
          std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
            result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant array AO set to bottom "
    " with a abstract object set to top")
    {
      const auto &op1=
        util.build_bottom_array(array_type);
      const auto &op2=
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
          std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
            result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant array AO set to bottom with a AO set to bottom")
    {
      const auto &op1=
        util.build_bottom_array(array_type);
      const auto &op2=
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
          std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
            result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging AO set to top with a constant array AO with a value")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=util.build_array(val1);

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
    WHEN("Merging AO set to top with a constant array AO set to top")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=
        util.build_top_array(array_type);

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
    WHEN("Merging AO set to top with a constant array AO set to bottom")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=
        util.build_bottom_array(array_type);

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
    WHEN("Merging AO set to bottom with a constant array AO with a value")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=util.build_array(val1);

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
    WHEN("Merging AO set to bottom with a constant array AO set to top")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=
        util.build_top_array(array_type);

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
    WHEN("Merging AO set to bottom with a constant array AO set to bottom")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=
        util.build_bottom_array(array_type);

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
