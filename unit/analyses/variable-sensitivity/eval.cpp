// Copyright 2016-2020 Diffblue Limited.

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

static symbolt simple_symbol(const irep_idt &identifier, const typet &type)
{
  symbolt b1;
  b1.name = b1.base_name = b1.pretty_name = identifier;
  b1.type = type;
  return b1;
}

SCENARIO(
  "eval",
  "[core][analyses][variable-sensitivity][interval_abstract_value]")
{
  GIVEN("An environment with intervals domain")
  {
    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::intervals());
    abstract_environmentt environment(object_factory);
    environment.make_top(); // Domains are bottom on construction

    symbol_tablet symbol_table;
    namespacet ns{symbol_table};

    signedbv_typet number_type{32};
    const auto &b1 = simple_symbol("b1", number_type);
    symbol_table.add(b1);

    WHEN("Evaluating expression with an unknown value")
    {
      // b1 == 0 ? 1 : 0
      if_exprt condition{
        equal_exprt{b1.symbol_expr(), from_integer(0, number_type)},
        from_integer(1, number_type),
        from_integer(0, number_type)};

      const auto result = environment.eval(condition, ns);

      THEN("Should get a wrapped range of 0..1")
      {
        REQUIRE(
          std::dynamic_pointer_cast<const context_abstract_objectt>(result));
        REQUIRE_FALSE(result->is_top());
        REQUIRE_FALSE(result->is_bottom());
        auto result_as_interval =
          std::dynamic_pointer_cast<const interval_abstract_valuet>(
            result->unwrap_context());
        REQUIRE(result_as_interval);
        REQUIRE(
          result_as_interval->to_interval().get_lower() ==
          from_integer(0, number_type));
        REQUIRE(
          result_as_interval->to_interval().get_upper() ==
          from_integer(1, number_type));
      }

      WHEN("Assigning the symbol a value")
      {
        // b1 = 0
        environment.assign(
          b1.symbol_expr(),
          object_factory->get_abstract_object(
            number_type,
            false,
            false,
            from_integer(0, number_type),
            environment,
            ns),
          ns);

        const auto result_after_assignment = environment.eval(condition, ns);

        THEN("Should get a wrapped interval of one element")
        {
          REQUIRE(std::dynamic_pointer_cast<const context_abstract_objectt>(
            result_after_assignment));
          const auto unwrapped =
            std::dynamic_pointer_cast<const context_abstract_objectt>(
              result_after_assignment)
              ->unwrap_context();
          auto result_as_interval =
            std::dynamic_pointer_cast<const interval_abstract_valuet>(
              unwrapped);
          REQUIRE(result_as_interval);
          REQUIRE(
            result_as_interval->to_constant() == from_integer(1, number_type));
        }
      }
    }
  }
}
