/*******************************************************************\

 Module: Unit tests for full_struct_abstract_object::merge

 Author: DiffBlue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <typeinfo>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object/struct_builder.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

SCENARIO(
  "merge_full_struct_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][full_struct_abstract_object][merge]")
{
  GIVEN("Two structs with 3 components, whose 1st component are the same")
  {
    // struct val1 = {.a = 1, .b = 2, .c = 3}
    auto val1 = std::map<std::string, int>{{"a", 1}, {"b", 2}, {"c", 3}};

    // struct val2 = {.a = 1, .b = 4, .c = 5}
    auto val2 = std::map<std::string, int>{{"a", 1}, {"b", 4}, {"c", 5}};

    // member_exprt for reading from a struct
    exprt dummy = nil_exprt{};
    dummy.type() = struct_typet{
      {{"a", integer_typet{}}, {"b", integer_typet{}}, {"c", integer_typet{}}}};
    const auto a = member_exprt(dummy, "a", integer_typet());
    const auto b = member_exprt(dummy, "b", integer_typet());
    const auto c = member_exprt(dummy, "c", integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::constant_domain());
    abstract_environmentt environment(object_factory);
    environment.make_top();
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("Merging two constant struct AOs with the same contents")
    {
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = build_struct(val1, environment, ns);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(
          read_component(cast_result, a, environment, ns) ==
          to_expr(val1["a"]));
        REQUIRE(
          read_component(cast_result, b, environment, ns) ==
          to_expr(val1["b"]));
        REQUIRE(
          read_component(cast_result, c, environment, ns) ==
          to_expr(val1["c"]));

        // Is optimal
        REQUIRE_FALSE(result.modified);
      }
    }
    WHEN("Merging two constant struct AOs with the different contents")
    {
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = build_struct(val2, environment, ns);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(
          read_component(cast_result, a, environment, ns) ==
          to_expr(val1["a"]));
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // Since it has modified, we definitely shouldn't be reusing the pointer
        REQUIRE(result.modified);
        REQUIRE_FALSE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO with a value "
      "with a constant struct AO set to top")
    {
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = build_top_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(read_component(cast_result, a, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // We can't reuse the abstract object as the value has changed
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO with a value "
      "with a constant struct AO set to bottom")
    {
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = build_bottom_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(
          read_component(cast_result, a, environment, ns) ==
          to_expr(val1["a"]));
        REQUIRE(
          read_component(cast_result, b, environment, ns) ==
          to_expr(val1["b"]));
        REQUIRE(
          read_component(cast_result, c, environment, ns) ==
          to_expr(val1["c"]));

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO with a value")
    {
      auto op1 = build_top_struct();
      auto op2 = build_struct(val1, environment, ns);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(read_component(cast_result, a, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO set to top")
    {
      auto op1 = build_top_struct();
      auto op2 = build_top_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(read_component(cast_result, a, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to top "
      "with a constant struct AO set to bottom")
    {
      auto op1 = build_top_struct();
      auto op2 = build_bottom_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(read_component(cast_result, a, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO with a value")
    {
      auto op1 = build_bottom_struct();
      auto op2 = build_struct(val1, environment, ns);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(
          read_component(cast_result, a, environment, ns) ==
          to_expr(val1["a"]));
        REQUIRE(
          read_component(cast_result, b, environment, ns) ==
          to_expr(val1["b"]));
        REQUIRE(
          read_component(cast_result, c, environment, ns) ==
          to_expr(val1["c"]));

        // Is optimal
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO set to top")
    {
      auto op1 = build_bottom_struct();
      auto op2 = build_top_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(read_component(cast_result, a, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, b, environment, ns) == nil_exprt());
        REQUIRE(read_component(cast_result, c, environment, ns) == nil_exprt());

        // Is optimal
        REQUIRE(result.modified);
        REQUIRE(result.object != op1);
      }
    }
    WHEN(
      "Merging a constant struct AO set to bottom "
      "with a constant struct AO set to bottom")
    {
      auto op1 = build_bottom_struct();
      auto op2 = build_bottom_struct();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = make_top_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
      auto op1 = build_struct(val1, environment, ns);
      auto op2 = make_bottom_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      auto cast_result =
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
        REQUIRE(
          read_component(cast_result, a, environment, ns) ==
          to_expr(val1["a"]));
        REQUIRE(
          read_component(cast_result, b, environment, ns) ==
          to_expr(val1["b"]));
        REQUIRE(
          read_component(cast_result, c, environment, ns) ==
          to_expr(val1["c"]));

        // Is optimal
        REQUIRE_FALSE(result.modified);
        REQUIRE(result.object == op1);
      }
    }
    WHEN(
      "Merging constant struct AO set to top "
      "with a abstract object set to top")
    {
      auto op1 = build_top_struct();
      auto op2 = make_top_object();

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
        auto cast_result =
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
      auto op1 = build_top_struct();
      auto op2 = make_bottom_object();

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
        auto cast_result =
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
      auto op1 = build_bottom_struct();
      auto op2 = make_top_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);
      THEN("Return a new top abstract object of the same type")
      {
        // Simple correctness of merge
        REQUIRE(result.modified);
        REQUIRE(result.object->is_top());
        REQUIRE_FALSE(result.object->is_bottom());

        // We don't optimize for returning the second parameter if we can

        // Is type still correct
        auto cast_result =
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging constant struct AO set to bottom with a AO set to bottom")
    {
      auto op1 = build_bottom_struct();
      auto op2 = make_bottom_object();

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
        auto cast_result =
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result.object);
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(cast_result);
      }
    }
    WHEN("Merging AO set to top with a constant struct AO with a value")
    {
      auto op2 = build_struct(val1, environment, ns);
      auto op1 = make_top_object();

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
      auto op2 = build_top_struct();
      auto op1 = make_top_object();

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
      auto op2 = build_bottom_struct();
      auto op1 = make_top_object();

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
      auto op2 = build_struct(val1, environment, ns);
      auto op1 = make_bottom_object();

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
      auto op2 = build_top_struct();
      auto op1 = make_bottom_object();

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
      auto op2 = build_bottom_struct();
      auto op1 = make_bottom_object();

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
