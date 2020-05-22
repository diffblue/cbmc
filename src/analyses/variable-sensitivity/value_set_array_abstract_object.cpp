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

abstract_object_pointert value_set_array_abstract_objectt::read(
  const abstract_environmentt &env,
  const exprt &specifier,
  const namespacet &ns) const
{
  return array_abstract_objectt::read(env, specifier, ns);
}

abstract_object_pointert value_set_array_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  std::stack<exprt> stack,
  const exprt &specifier,
  abstract_object_pointert value,
  bool merging_write) const
{
  return array_abstract_objectt::write(
    environment, ns, stack, specifier, value, merging_write);
}

abstract_object_pointert value_set_array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet &ns) const
{
  return array_abstract_objectt::read_index(env, index, ns);
}

sharing_ptrt<array_abstract_objectt>
value_set_array_abstract_objectt::write_index(
  abstract_environmentt &environment,
  const namespacet &ns,
  std::stack<exprt> stack,
  const index_exprt &index_expr,
  abstract_object_pointert value,
  bool merging_write) const
{
  return array_abstract_objectt::write_index(
    environment, ns, stack, index_expr, value, merging_write);
}
