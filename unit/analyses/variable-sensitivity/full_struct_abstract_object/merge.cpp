/*******************************************************************\

 Module: Unit tests for full_struct_abstract_object::merge

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
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

typedef full_array_abstract_objectt::full_array_pointert
  full_array_abstract_object_pointert;

// Util

class struct_utilt
{
public:
  struct_utilt(abstract_environmentt &enviroment, const namespacet &ns)
    : enviroment(enviroment), ns(ns)
  {
  }

  exprt read_component(
    full_struct_abstract_objectt::constant_struct_pointert struct_object,
    const member_exprt &component) const
  {
    return struct_object->expression_transform(component, {}, enviroment, ns)
      ->to_constant();
  }

  // At the moment the full_struct_abstract_object does not support
  // initialization directly from an exprt so we manually write the components
  full_struct_abstract_objectt::constant_struct_pointert
  build_struct(const struct_exprt &starting_value)
  {
    std::shared_ptr<const full_struct_abstract_objectt> result =
      std::make_shared<const full_struct_abstract_objectt>(
        starting_value, enviroment, ns);

    struct_typet struct_type(to_struct_type(starting_value.type()));
    size_t comp_index = 0;
    for(const exprt &op : starting_value.operands())
    {
      const auto &component = struct_type.components()[comp_index];
      std::shared_ptr<const abstract_objectt> new_result = result->write(
        enviroment,
        ns,
        std::stack<exprt>(),
        member_exprt(nil_exprt(), component.get_name(), component.type()),
        enviroment.eval(op, ns),
        false);
      result = std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
        new_result);

      ++comp_index;
    }

    return result;
  }

  full_struct_abstract_objectt::constant_struct_pointert
  build_top_struct(const typet &struct_type)
  {
    return std::make_shared<full_struct_abstract_objectt>(
      struct_type, true, false);
  }

  full_struct_abstract_objectt::constant_struct_pointert
  build_bottom_struct(const typet &struct_type)
  {
    return std::make_shared<full_struct_abstract_objectt>(
      struct_type, false, true);
  }

private:
  abstract_environmentt &enviroment;
  const namespacet ns;
};

SCENARIO(
  "merge_full_struct_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][full_struct_abstract_object][merge]")
{
  GIVEN("Two structs with 3 components, whose 1st component are the same")
  {
    // struct val1 = {.a = 1, .b = 2, .c = 3}
    struct_typet struct_type;
    struct_union_typet::componentt comp_a("a", integer_typet());
    struct_union_typet::componentt comp_b("b", integer_typet());
    struct_union_typet::componentt comp_c("c", integer_typet());
    struct_type.components().push_back(comp_a);
    struct_type.components().push_back(comp_b);
    struct_type.components().push_back(comp_c);

    exprt::operandst val1_op;
    val1_op.push_back(from_integer(1, integer_typet()));
    val1_op.push_back(from_integer(2, integer_typet()));
    val1_op.push_back(from_integer(3, integer_typet()));
    struct_exprt val1(val1_op, struct_type);

    // struct val1 = {.a = 1, .b = 4, .c = 5}
    exprt::operandst val2_op;
    val2_op.push_back(from_integer(1, integer_typet()));
    val2_op.push_back(from_integer(4, integer_typet()));
    val2_op.push_back(from_integer(5, integer_typet()));
    struct_exprt val2(val2_op, struct_type);

    // index_exprt for reading from an array
    const member_exprt a(nil_exprt(), "a", integer_typet());
    const member_exprt b(nil_exprt(), "b", integer_typet());
    const member_exprt c(nil_exprt(), "c", integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::constant_domain());
    abstract_environmentt enviroment(object_factory);
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    struct_utilt util(enviroment, ns);

    WHEN("Merging two constant struct AOs with the same contents")
    {
      auto op1 = util.build_struct(val1);
      auto op2 = util.build_struct(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("The original struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == val1.op0());
        REQUIRE(util.read_component(cast_result, b) == val1.op1());
        REQUIRE(util.read_component(cast_result, c) == val1.op2());

        // Is optimal
        REQUIRE_FALSE(result.modified);
      }
    }
    WHEN("Merging two constant struct AOs with the different contents")
    {
      auto op1 = util.build_struct(val1);
      auto op2 = util.build_struct(val2);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN(
        "A new constant struct AO whose a component is the same and the "
        "b and c are set to top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == val1.op0());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE(result.modified);
        REQUIRE_FALSE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO with a value "
      "with a constant struct AO set to top")
    {
      auto op1 = util.build_struct(val1);
      auto op2 = util.build_top_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("A new constant struct AO set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == nil_exprt());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // We can't reuse the abstract object as the value has changed
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO with a value "
      "with a constant struct AO set to bottom")
    {
      auto op1 = util.build_struct(val1);
      auto op2 = util.build_bottom_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("The original const AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == val1.op0());
        REQUIRE(util.read_component(cast_result, b) == val1.op1());
        REQUIRE(util.read_component(cast_result, c) == val1.op2());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO with a value")
    {
      auto op1 = util.build_top_struct(struct_type);
      auto op2 = util.build_struct(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == nil_exprt());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO set to top")
    {
      auto op1 = util.build_top_struct(struct_type);
      auto op2 = util.build_top_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == nil_exprt());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO set to bottom")
    {
      auto op1 = util.build_top_struct(struct_type);
      auto op2 = util.build_bottom_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == nil_exprt());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO with a value")
    {
      auto op1 = util.build_bottom_struct(struct_type);
      auto op2 = util.build_struct(val1);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("A new AO should be returned with op2s valuee")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == val1.op0());
        REQUIRE(util.read_component(cast_result, b) == val1.op1());
        REQUIRE(util.read_component(cast_result, c) == val1.op2());

        // Is optimal
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO set to top")
    {
      auto op1 = util.build_bottom_struct(struct_type);
      auto op2 = util.build_top_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("A new constant struct AO should be returned set to top ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(result.modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == nil_exprt());
        REQUIRE(util.read_component(cast_result, b) == nil_exprt());
        REQUIRE(util.read_component(cast_result, c) == nil_exprt());

        // Is optimal
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO set to bottom")
    {
      auto op1 = util.build_bottom_struct(struct_type);
      auto op2 = util.build_bottom_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
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
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant struct AO with value "
      "with a abstract object set to top")
    {
      const auto &op1 = util.build_struct(val1);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
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
      "Merging constant struct AO with value "
      "with a abstract object set to bottom")
    {
      const auto &op1 = util.build_struct(val1);
      const auto &op2 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      const auto &cast_result =
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          result.object);
      THEN("We should get the same constant struct AO back")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a) == val1.op0());
        REQUIRE(util.read_component(cast_result, b) == val1.op1());
        REQUIRE(util.read_component(cast_result, c) == val1.op2());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant struct AO set to top "
      "with a abstract object set to top")
    {
      const auto &op1 = util.build_top_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN(
      "Merging constant struct AO set to top "
      "with a abstract object set to bottom")
    {
      const auto &op1 = util.build_top_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN(
      "Merging constant struct AO set to bottom "
      " with a abstract object set to top")
    {
      const auto &op1 = util.build_bottom_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant struct AO set to bottom with a AO set to bottom")
    {
      const auto &op1 = util.build_bottom_struct(struct_type);
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
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);

        // Is type still correct
        const auto &cast_result =
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging AO set to top with a constant struct AO with a value")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_struct(val1);

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
    WHEN("Merging AO set to top with a constant struct AO set to top")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_top_struct(struct_type);

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
    WHEN("Merging AO set to top with a constant struct AO set to bottom")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2 = util.build_bottom_struct(struct_type);

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
    WHEN("Merging AO set to bottom with a constant struct AO with a value")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_struct(val1);

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
    WHEN("Merging AO set to bottom with a constant struct AO set to top")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_top_struct(struct_type);

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
    WHEN("Merging AO set to bottom with a constant struct AO set to bottom")
    {
      const auto &op1 =
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2 = util.build_bottom_struct(struct_type);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("The original AO should be returned")
      {
        // Simple correctness of merge
        REQUIRE_FALSE(result.modified);
        REQUIRE_FALSE(result.object->is_top());
        REQUIRE(result.object->is_bottom());

        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
  }
}
