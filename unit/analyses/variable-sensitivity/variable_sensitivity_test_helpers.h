/*******************************************************************\

 Module: Unit tests helpers for value_set_abstract_objects

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns);

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, bool top);

std::shared_ptr<const constant_abstract_valuet> make_top_constant();

std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns);

std::shared_ptr<value_set_abstract_objectt> make_value_set(
  const std::vector<exprt> &vals,
  abstract_environmentt &env,
  namespacet &ns);

std::shared_ptr<value_set_abstract_objectt> make_top_value_set();

std::shared_ptr<const constant_abstract_valuet>
as_constant(const abstract_object_pointert &aop);

std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop);

bool set_contains(const abstract_object_sett &set, const exprt &val);

void EXPECT(
  std::shared_ptr<const constant_abstract_valuet> &result,
  exprt expected_value);

void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

void EXPECT_TOP(std::shared_ptr<const abstract_objectt> result);

void EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result);

void EXPECT_BOTTOM(std::shared_ptr<const abstract_objectt> result);

void EXPECT_UNMODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified);

void EXPECT_UNMODIFIED(
  std::shared_ptr<const constant_abstract_valuet> &result,
  bool modified,
  exprt expected_value);

void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values);

std::shared_ptr<const constant_abstract_valuet> add_as_constant(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns);

std::shared_ptr<const value_set_abstract_objectt> add_as_value_set(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns);
std::shared_ptr<const value_set_abstract_objectt> add_as_value_set(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  const abstract_object_pointert &op3,
  abstract_environmentt &environment,
  namespacet &ns);
