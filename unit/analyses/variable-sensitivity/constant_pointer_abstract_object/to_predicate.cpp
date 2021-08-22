/*******************************************************************\

 Module: Tests for constant_pointer_abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/pointer_expr.h>
#include <util/symbol_table.h>

SCENARIO(
  "constant_pointer_abstract_object to predicate",
  "[core][analyses][variable-sensitivity][constant_pointer_abstract_object][to_"
  "predicate]")
{
  const auto int_type = signedbv_typet(32);
  const auto ptr_type = pointer_typet(int_type, 32);
  const auto val2_symbol = symbol_exprt(dstringt("val2"), int_type);

  const auto x_name = symbol_exprt(dstringt("x"), int_type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("constant_pointer_abstract_object")
  {
    WHEN("it is TOP")
    {
      auto obj = std::make_shared<constant_pointer_abstract_objectt>(
        ptr_type, true, false);
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = std::make_shared<constant_pointer_abstract_objectt>(
        ptr_type, false, true);
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("points to a &symbol")
    {
      const auto address_of = address_of_exprt(val2_symbol);
      auto obj = std::make_shared<constant_pointer_abstract_objectt>(
        address_of, environment, ns);
      THEN_PREDICATE(obj, "x == &val2");
    }
  }
}
