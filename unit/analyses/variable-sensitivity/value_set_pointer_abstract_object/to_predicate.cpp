/*******************************************************************\

 Module: Tests for value_set_pointer_abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/value_set_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/pointer_expr.h>
#include <util/symbol_table.h>

template <typename... Args>
std::shared_ptr<value_set_pointer_abstract_objectt> make_vsp(Args &&... args)
{
  return std::make_shared<value_set_pointer_abstract_objectt>(
    std::forward<Args>(args)...);
}

SCENARIO(
  "value_set_pointer_abstract_object to predicate",
  "[core][analyses][variable-sensitivity][value_set_pointer_abstract_object]["
  "to_predicate]")
{
  const auto int_type = signedbv_typet(32);
  const auto ptr_type = pointer_typet(int_type, 32);
  const auto val1_symbol = symbol_exprt(dstringt("val1"), int_type);
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

  GIVEN("value_set_pointer_abstract_object")
  {
    WHEN("it is TOP")
    {
      auto obj = make_vsp(ptr_type, true, false);
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = make_vsp(ptr_type, false, true);
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("points to a &symbol")
    {
      const auto address_of = address_of_exprt(val2_symbol);
      auto obj = make_vsp(address_of, environment, ns);
      THEN_PREDICATE(obj, "x == &val2");
    }
    WHEN("points to { &val1, &val2 } ")
    {
      auto address_of_val1 = address_of_exprt(val1_symbol);
      auto address_of_val2 = address_of_exprt(val2_symbol);
      auto p1 = make_vsp(address_of_val1, environment, ns);
      auto p2 = make_vsp(address_of_val2, environment, ns);

      auto obj = abstract_objectt::merge(p1, p2, widen_modet::no).object;
      THEN_PREDICATE(obj, "x == &val1 || x == &val2");
    }
  }
}
