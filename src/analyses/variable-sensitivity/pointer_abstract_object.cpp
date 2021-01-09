/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <util/std_expr.h>
#include <util/std_types.h>

#include <analyses/variable-sensitivity/abstract_environment.h>

#include "pointer_abstract_object.h"

pointer_abstract_objectt::pointer_abstract_objectt(const typet &t)
  : abstract_objectt(t)
{
  PRECONDITION(t.id() == ID_pointer);
}

pointer_abstract_objectt::pointer_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_objectt(type, top, bottom)
{
  PRECONDITION(type.id() == ID_pointer);
}

pointer_abstract_objectt::pointer_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(e, environment, ns)
{
  PRECONDITION(e.type().id() == ID_pointer);
}

abstract_object_pointert pointer_abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(expr.id() == ID_dereference)
  {
    return read_dereference(environment, ns);
  }

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert pointer_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return write_dereference(environment, ns, stack, value, merging_write);
}

abstract_object_pointert pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  pointer_typet pointer_type(to_pointer_type(type()));
  const typet &pointed_to_type = pointer_type.subtype();

  return env.abstract_object_factory(pointed_to_type, ns, true, false);
}

#include <iostream>

abstract_object_pointert pointer_abstract_objectt::write_dereference(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    environment.havoc("Writing to a 2value pointer");
    return shared_from_this();
  }
  else
  {
    return std::make_shared<pointer_abstract_objectt>(type(), true, false);
  }
}

void pointer_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_pointers;
}
