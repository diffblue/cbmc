/*******************************************************************\

 Module: Unit tests helpers for value_set_abstract_objects

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns);

std::shared_ptr<const constant_abstract_valuet> make_top_constant();
std::shared_ptr<const constant_abstract_valuet> make_bottom_constant();

std::shared_ptr<const interval_abstract_valuet> make_interval(
  const exprt &vall,
  const exprt &valh,
  abstract_environmentt &env,
  namespacet &ns);
std::shared_ptr<const interval_abstract_valuet> make_interval(
  const constant_interval_exprt &val,
  abstract_environmentt &env,
  namespacet &ns);
std::shared_ptr<const interval_abstract_valuet> make_top_interval();
std::shared_ptr<const interval_abstract_valuet> make_bottom_interval();

std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns);

std::shared_ptr<value_set_abstract_objectt> make_value_set(
  const std::vector<exprt> &vals,
  abstract_environmentt &env,
  namespacet &ns);

std::shared_ptr<value_set_abstract_objectt> make_top_value_set();

abstract_object_pointert make_bottom_object();
abstract_object_pointert make_top_object();

std::shared_ptr<const constant_abstract_valuet>
as_constant(const abstract_object_pointert &aop);

std::shared_ptr<const interval_abstract_valuet>
as_interval(const abstract_object_pointert &aop);

std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop);

bool set_contains(const abstract_object_sett &set, const exprt &val);

void EXPECT(
  std::shared_ptr<const constant_abstract_valuet> &result,
  exprt expected_value);

void EXPECT(
  std::shared_ptr<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value);

void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

void EXPECT(
  const std::vector<exprt> &values,
  const std::vector<exprt> &expected_values);

void EXPECT_TOP(std::shared_ptr<const abstract_objectt> result);

void EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result);

void EXPECT_BOTTOM(std::shared_ptr<const abstract_objectt> result);

template <class value_typet>
struct merge_result
{
  bool modified;
  std::shared_ptr<const value_typet> result;
};

void EXPECT_UNMODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified);

template <class abstract_typet>
void EXPECT_UNMODIFIED(merge_result<const abstract_typet> &result)
{
  auto ao = std::dynamic_pointer_cast<const abstract_objectt>(result.result);
  EXPECT_UNMODIFIED(ao, result.modified);
}

template <class abstract_typet>
void EXPECT_UNMODIFIED_TOP(merge_result<const abstract_typet> &result)
{
  auto ao = std::dynamic_pointer_cast<const abstract_objectt>(result.result);
  EXPECT_UNMODIFIED(ao, result.modified);
  EXPECT_TOP(result.result);
}

template <class abstract_typet>
void EXPECT_UNMODIFIED_BOTTOM(merge_result<const abstract_typet> &result)
{
  auto ao = std::dynamic_pointer_cast<const abstract_objectt>(result.result);
  EXPECT_UNMODIFIED(ao, result.modified);
  EXPECT_BOTTOM(result.result);
}

template <class abstract_typet>
void EXPECT_MODIFIED_TOP(merge_result<const abstract_typet> &result)
{
  auto ao = std::dynamic_pointer_cast<const abstract_objectt>(result.result);
  EXPECT_MODIFIED(ao, result.modified);
  EXPECT_TOP(result.result);
}

void EXPECT_MODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified);

template <class abstract_typet>
void EXPECT_MODIFIED(merge_result<const abstract_typet> &result)
{
  auto ao = std::dynamic_pointer_cast<const abstract_objectt>(result.result);
  EXPECT_MODIFIED(ao, result.modified);
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const constant_abstract_valuet> &result,
  bool modified,
  exprt expected_value);

void EXPECT_UNMODIFIED(
  merge_result<const constant_abstract_valuet> &result,
  exprt expected_value);

void EXPECT_UNMODIFIED(
  std::shared_ptr<const interval_abstract_valuet> &result,
  bool modified,
  exprt lower_value,
  exprt upper_value);

void EXPECT_UNMODIFIED(
  merge_result<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value);

void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values);

void EXPECT_UNMODIFIED(
  merge_result<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

void EXPECT_MODIFIED(
  std::shared_ptr<const constant_abstract_valuet> &result,
  bool modified,
  exprt expected_value);

void EXPECT_MODIFIED(
  merge_result<const constant_abstract_valuet> &result,
  exprt expected_value);

void EXPECT_MODIFIED(
  std::shared_ptr<const interval_abstract_valuet> &result,
  bool modified,
  exprt lower_value,
  exprt upper_value);

void EXPECT_MODIFIED(
  merge_result<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value);

void EXPECT_MODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values);

void EXPECT_MODIFIED(
  merge_result<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

std::shared_ptr<const abstract_objectt> add(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns);

std::shared_ptr<const constant_abstract_valuet> add_as_constant(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns);

std::shared_ptr<const interval_abstract_valuet> add_as_interval(
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
