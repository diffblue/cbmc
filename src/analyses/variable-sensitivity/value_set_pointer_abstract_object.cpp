
/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_pointer_abstract_object.h"

abstract_object_pointert
value_set_pointer_abstract_objectt::merge(abstract_object_pointert other) const
{
  return shared_from_this();
}

abstract_object_pointert value_set_pointer_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return pointer_abstract_objectt::write(
    environment, ns, stack, specifier, value, merging_write);
}

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const typet &type)
  : pointer_abstract_objectt(type)
{
}

abstract_object_pointert value_set_pointer_abstract_objectt::write_dereference(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return pointer_abstract_objectt::write_dereference(
    environment, ns, stack, value, merging_write);
}
