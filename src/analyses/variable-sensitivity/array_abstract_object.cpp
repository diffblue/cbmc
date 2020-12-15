/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include "array_abstract_object.h"
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/std_expr.h>
#include <util/std_types.h>

array_abstract_objectt::array_abstract_objectt(const typet &t)
  : abstract_objectt(t)
{
  PRECONDITION(t.id() == ID_array);
}

array_abstract_objectt::array_abstract_objectt(
  const typet &t,
  bool tp,
  bool bttm)
  : abstract_objectt(t, tp, bttm)
{
  PRECONDITION(t.id() == ID_array);
}

array_abstract_objectt::array_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(e, environment, ns)
{
  PRECONDITION(e.type().id() == ID_array);
}

abstract_object_pointert array_abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(expr.id() == ID_index)
  {
    return read_index(environment, to_index_expr(expr), ns);
  }

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert array_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return this->write_index(
    environment, ns, stack, to_index_expr(specifier), value, merging_write);
}

abstract_object_pointert array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet &ns) const
{
  array_typet array_type(to_array_type(type()));
  const typet &subtype = array_type.subtype();

  // if we are bottom then so are the values in the array
  // otherwise the values are top
  return env.abstract_object_factory(subtype, ns, !is_bottom(), is_bottom());
}

abstract_object_pointert array_abstract_objectt::write_index(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const index_exprt &index_expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  // TODO(tkiley): Should this in fact havoc since we can't verify
  // that we are not writing past the end of the array - Martin said
  // default should be not to, but perhaps for soundness the base class should
  // havoc and the default should derive from this.
  if(is_top() || is_bottom())
  {
    return shared_from_this();
  }
  else
  {
    return std::make_shared<array_abstract_objectt>(type(), true, false);
  }
}

void array_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_arrays;
}
