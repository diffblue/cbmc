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

typedef constant_array_abstract_objectt::constant_array_abstract_object_pointert
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
    return struct_object->read_component(
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
      std::shared_ptr<const struct_abstract_objectt> new_result=
        result->write_component(
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

private:
  abstract_environmentt &enviroment;
  const namespacet ns;
};

TEST_CASE("merge_full_struct_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][full_struct_abstract_object][merge]")
{
  // int val1[3] = {1, 2, 3}
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

  // int val2[3] = {1, 4, 5}
  struct_exprt val2(struct_type);
  val2.operands().push_back(constant_exprt::integer_constant(1));
  val2.operands().push_back(constant_exprt::integer_constant(4));
  val2.operands().push_back(constant_exprt::integer_constant(5));

  // index_exprt for reading from an array
  const member_exprt a(nil_exprt(), "a");
  const member_exprt b(nil_exprt(), "b");
  const member_exprt c(nil_exprt(), "c");

  abstract_environmentt enviroment;
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

  SECTION("constant struct AO merge with constant struct AO")
  {
    SECTION("merge struct with...")
    {
      auto op1=util.build_struct(val1);

      SECTION("same value")
      {
        INFO(val1.op0().type().id_string());

        auto op2=util.build_struct(val1);

        REQUIRE(util.read_component(op1, b)==val1.op1());
        REQUIRE(util.read_component(op1, a)==val1.op0());

        INFO(c.pretty());

        const exprt &arr_val2=util.read_component(op1, c);
        INFO(arr_val2.pretty());

        REQUIRE(arr_val2==val1.op2());

        REQUIRE(util.read_component(op2, a)==val1.op0());
        REQUIRE(util.read_component(op2, b)==val1.op1());
        REQUIRE(util.read_component(op2, c)==val1.op2());

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result);
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
      SECTION("different array")
      {
        abstract_object_pointert op2=util.build_struct(val2);

        result=abstract_objectt::merge(op1, op2, modified);

        const auto &cast_result=
          std::dynamic_pointer_cast<const full_struct_abstract_objectt>(
            result);
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
  }
}
