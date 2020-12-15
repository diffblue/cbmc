/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "struct_abstract_object.h"

struct_abstract_objectt::struct_abstract_objectt(const typet &t)
  : abstract_objectt(t)
{
  PRECONDITION(t.id() == ID_struct);
}

struct_abstract_objectt::struct_abstract_objectt(
  const typet &t,
  bool tp,
  bool bttm)
  : abstract_objectt(t, tp, bttm)
{
  PRECONDITION(t.id() == ID_struct);
}

struct_abstract_objectt::struct_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(e, environment, ns)
{
  PRECONDITION(ns.follow(e.type()).id() == ID_struct);
}

abstract_object_pointert struct_abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(expr.id() == ID_member)
  {
    return read_component(environment, to_member_expr(expr), ns);
  }

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert struct_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return this->write_component(
    environment, ns, stack, to_member_expr(specifier), value, merging_write);
}

abstract_object_pointert struct_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const member_exprt &member_expr,
  const namespacet &ns) const
{
  // If we are bottom then so are the components
  // otherwise the components could be anything
  return environment.abstract_object_factory(
    member_expr.type(), ns, !is_bottom(), is_bottom());
}

abstract_object_pointert struct_abstract_objectt::write_component(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const member_exprt &member_expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    return shared_from_this();
  }
  else
  {
    return std::make_shared<struct_abstract_objectt>(type(), true, false);
  }
}

void struct_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_structs;
}
