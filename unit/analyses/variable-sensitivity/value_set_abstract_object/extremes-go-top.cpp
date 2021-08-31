/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "value-sets spanning min-max go TOP",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][extreme]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());

  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

  GIVEN("{FALSE, TRUE} goes TOP")
  {
    auto boolInterval =
      make_value_set({false_exprt(), true_exprt()}, environment, ns);

    EXPECT_TOP(boolInterval);
  }
  GIVEN("{min(bool), max(bool)} goes TOP")
  {
    auto boolInterval = make_value_set(
      {min_exprt(bool_typet()), max_exprt(bool_typet())}, environment, ns);

    EXPECT_TOP(boolInterval);
  }
  GIVEN("{0, 1} c_bool goes TOP")
  {
    auto c_bool_type = bitvector_typet(ID_c_bool, 8);
    auto boolInterval = make_value_set(
      {from_integer(0, c_bool_type), from_integer(1, c_bool_type)},
      environment,
      ns);

    EXPECT_TOP(boolInterval);
  }
  GIVEN("{min(c_bool), max(c_bool)} goes TOP")
  {
    auto c_bool_type = bitvector_typet(ID_c_bool, 8);
    auto boolInterval = make_value_set(
      {min_exprt(c_bool_type), max_exprt(c_bool_type)}, environment, ns);

    EXPECT_TOP(boolInterval);
  }
}
