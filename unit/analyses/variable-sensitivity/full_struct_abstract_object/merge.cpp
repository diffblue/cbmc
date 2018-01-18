/*******************************************************************\

 Module: Unit tests for full_struct_abstract_object::merge

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
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>


#include <iostream>

typedef constant_array_abstract_objectt::constant_array_pointert
  constant_array_abstract_object_pointert;

// Util


class struct_utilt
{
public:
  struct_utilt(abstract_environmentt &enviroment, const namespacet &ns):
    enviroment(enviroment), ns(ns)
  {}

  exprt read_component(
    full_struct_abstract_objectt::constant_struct_pointert struct_object,
    const member_exprt &component) const
  {
    return struct_object->read(
      enviroment, component, ns)->to_constant();
  }

  // At the moment the full_struct_abstract_object does not support
  // initialization directly from an exprt so we manually write the components
  full_struct_abstract_objectt::constant_struct_pointert build_struct(
    const struct_exprt &starting_value)
  {
    std::shared_ptr<const full_struct_abstract_objectt> result=
      std::make_shared<const full_struct_abstract_objectt>(
        starting_value, enviroment, ns);

    struct_typet struct_type(to_struct_type(starting_value.type()));
    size_t comp_index=0;
    for(const exprt &op : starting_value.operands())
    {
      const auto &component=struct_type.components()[comp_index];
      std::shared_ptr<const abstract_objectt> new_result=
        result->write(
          enviroment,
          ns,
          std::stack<exprt>(),
          member_exprt(nil_exprt(), component.get_name()),
          enviroment.eval(op, ns),
          false);
      result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
          new_result);

      ++comp_index;
    }

    return result;
  }

  full_struct_abstract_objectt::constant_struct_pointert build_top_struct(
    const typet &struct_type)
  {
    return std::make_shared<full_struct_abstract_objectt>(
        struct_type, true, false);
  }

  full_struct_abstract_objectt::constant_struct_pointert build_bottom_struct(
    const typet &struct_type)
  {
    return std::make_shared<full_struct_abstract_objectt>(
        struct_type, false, true);
  }

private:
  abstract_environmentt &enviroment;
  const namespacet ns;
};

SCENARIO("merge_full_struct_abstract_object",
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

    struct_exprt val1(struct_type);
    val1.operands().push_back(constant_exprt::integer_constant(1));
    val1.operands().push_back(constant_exprt::integer_constant(2));
    val1.operands().push_back(constant_exprt::integer_constant(3));

    // struct val1 = {.a = 1, .b = 4, .c = 5}
    struct_exprt val2(struct_type);
    val2.operands().push_back(constant_exprt::integer_constant(1));
    val2.operands().push_back(constant_exprt::integer_constant(4));
    val2.operands().push_back(constant_exprt::integer_constant(5));

    // index_exprt for reading from an array
    const member_exprt a(nil_exprt(), "a");
    const member_exprt b(nil_exprt(), "b");
    const member_exprt c(nil_exprt(), "c");

    abstract_environmentt enviroment;
    enviroment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    optionst options;
    options.set_option("pointers", true);
    options.set_option("arrays", true);
    options.set_option("structs", true);
    variable_sensitivity_object_factoryt::instance().set_options(options);

    struct_utilt util(enviroment, ns);

    abstract_object_pointert result;
    bool modified=false;

    WHEN("Merging two constant struct AOs with the same contents")
    {
      auto op1=util.build_struct(val1);
      auto op2=util.build_struct(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("The original struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==val1.op0());
        REQUIRE(util.read_component(cast_result, b)==val1.op1());
        REQUIRE(util.read_component(cast_result, c)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging two constant struct AOs with the different contents")
    {
      auto op1=util.build_struct(val1);
      auto op2=util.build_struct(val2);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("A new constant struct AO whose a component is the same and the "
        "b and c are set to top")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==val1.op0());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());


        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE_FALSE(result==op1);
      }
    }
    WHEN("Merging a constant struct AO with a value "
      "with a constant struct AO set to top")
    {
      auto op1=util.build_struct(val1);
      auto op2=util.build_top_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("A new constant struct AO set to top should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==nil_exprt());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());

        // We can't reuse the abstract object as the value has changed
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant struct AO with a value "
      "with a constant struct AO set to bottom")
    {
      auto op1=util.build_struct(val1);
      auto op2=util.build_bottom_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("The original const AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==val1.op0());
        REQUIRE(util.read_component(cast_result, b)==val1.op1());
        REQUIRE(util.read_component(cast_result, c)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant struct AO set to top "
      "with a constant struct AO with a value")
    {
      auto op1=util.build_top_struct(struct_type);
      auto op2=util.build_struct(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==nil_exprt());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant struct AO set to top "
      "with a constant struct AO set to top")
    {
      auto op1=util.build_top_struct(struct_type);
      auto op2=util.build_top_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==nil_exprt());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant struct AO set to top "
      "with a constant struct AO set to bottom")
    {
      auto op1=util.build_top_struct(struct_type);
      auto op2=util.build_bottom_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("The original constant struct AO should be returned")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==nil_exprt());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging a constant struct AO set to bottom "
      "with a constant struct AO with a value")
    {
      auto op1=util.build_bottom_struct(struct_type);
      auto op2=util.build_struct(val1);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("A new AO should be returned with op2s valuee")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==val1.op0());
        REQUIRE(util.read_component(cast_result, b)==val1.op1());
        REQUIRE(util.read_component(cast_result, c)==val1.op2());

        // Is optimal
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant struct AO set to bottom "
      "with a constant struct AO set to top")
    {
      auto op1=util.build_bottom_struct(struct_type);
      auto op2=util.build_top_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("A new constant struct AO should be returned set to top ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==nil_exprt());
        REQUIRE(util.read_component(cast_result, b)==nil_exprt());
        REQUIRE(util.read_component(cast_result, c)==nil_exprt());

        // Is optimal
        REQUIRE(result!=op1);
      }
    }
    WHEN("Merging a constant struct AO set to bottom "
      "with a constant struct AO set to bottom")
    {
      auto op1=util.build_bottom_struct(struct_type);
      auto op2=util.build_bottom_struct(struct_type);

      result=abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
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
    WHEN("Merging constant struct AO with value "
      "with a abstract object set to top")
    {
      const auto &op1=util.build_struct(val1);
      const auto &op2=
        std::make_shared<abstract_objectt>(val1.type(), true, false);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);

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
    WHEN("Merging constant struct AO with value "
      "with a abstract object set to bottom")
    {
      const auto &op1=util.build_struct(val1);
      const auto &op2=
        std::make_shared<abstract_objectt>(val1.type(), false, true);

      bool modified;
      abstract_object_pointert result=
        abstract_objectt::merge(op1, op2, modified);

      const auto &cast_result=
        std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
      THEN("We should get the same constant struct AO back")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(cast_result->is_top());
        REQUIRE_FALSE(cast_result->is_bottom());
        REQUIRE(util.read_component(cast_result, a)==val1.op0());
        REQUIRE(util.read_component(cast_result, b)==val1.op1());
        REQUIRE(util.read_component(cast_result, c)==val1.op2());

        // Is optimal
        REQUIRE(result==op1);
      }
    }
    WHEN("Merging constant struct AO set to top "
      "with a abstract object set to top")
    {
      const auto &op1=
        util.build_top_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant struct AO set to top "
      "with a abstract object set to bottom")
    {
      const auto &op1=
        util.build_top_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant struct AO set to bottom "
    " with a abstract object set to top")
    {
      const auto &op1=
        util.build_bottom_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant struct AO set to bottom with a AO set to bottom")
    {
      const auto &op1=
        util.build_bottom_struct(struct_type);
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
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(result);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging AO set to top with a constant struct AO with a value")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=util.build_struct(val1);

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
    WHEN("Merging AO set to top with a constant struct AO set to top")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=
        util.build_top_struct(struct_type);

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
    WHEN("Merging AO set to top with a constant struct AO set to bottom")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), true, false);
      const auto &op2=
        util.build_bottom_struct(struct_type);

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
    WHEN("Merging AO set to bottom with a constant struct AO with a value")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=util.build_struct(val1);

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
    WHEN("Merging AO set to bottom with a constant struct AO set to top")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=
        util.build_top_struct(struct_type);

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
    WHEN("Merging AO set to bottom with a constant struct AO set to bottom")
    {
      const auto &op1=
        std::make_shared<abstract_objectt>(val1.type(), false, true);
      const auto &op2=
        util.build_bottom_struct(struct_type);

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
