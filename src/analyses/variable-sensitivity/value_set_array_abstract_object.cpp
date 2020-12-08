/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_array_abstract_object.h"

value_set_array_abstract_objectt::value_set_array_abstract_objectt(
  const typet &type)
  : array_abstract_objectt(type)
{
}

abstract_object_pointert value_set_array_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return array_abstract_objectt::write(
    environment, ns, stack, specifier, value, merging_write);
}

abstract_object_pointert value_set_array_abstract_objectt::write_index(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const index_exprt &index_expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return array_abstract_objectt::write_index(
    environment, ns, stack, index_expr, value, merging_write);
}
