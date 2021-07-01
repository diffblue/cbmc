/*******************************************************************\

 Module: Unit tests for interval_abstract_valuet

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static void
verify_extreme_interval(typet type, abstract_environmentt &env, namespacet &ns)
{
  auto interval = make_interval(min_exprt(type), max_exprt(type), env, ns);

  EXPECT_TOP(interval);
}

SCENARIO(
  "extreme intervals go TOP",
  "[core][analyses][variable-sensitivity][interval_abstract_value][extreme]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());

  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

  GIVEN("[min-max] signed goes TOP")
  {
    verify_extreme_interval(signedbv_typet(32), environment, ns);
  }
  GIVEN("[min-max] unsigned goes TOP")
  {
    verify_extreme_interval(unsignedbv_typet(32), environment, ns);
  }
  GIVEN("[min-max] bool goes TOP")
  {
    verify_extreme_interval(bool_typet(), environment, ns);
  }
  GIVEN("[min-max] c_bool goes TOP")
  {
    verify_extreme_interval(bitvector_typet(ID_c_bool, 8), environment, ns);
  }
  GIVEN("[FALSE, TRUE] goes TOP")
  {
    auto boolInterval =
      make_interval(false_exprt(), true_exprt(), environment, ns);

    EXPECT_TOP(boolInterval);
  }
  GIVEN("[0, 1] c_bool goes TOP")
  {
    auto c_bool_type = bitvector_typet(ID_c_bool, 8);
    auto boolInterval = make_interval(
      from_integer(0, c_bool_type),
      from_integer(1, c_bool_type),
      environment,
      ns);

    EXPECT_TOP(boolInterval);
  }
}
