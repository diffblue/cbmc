/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "union_abstract_object.h"

union_abstract_objectt::union_abstract_objectt(const typet &type)
  : abstract_objectt(type)
{
  PRECONDITION(type.id() == ID_union);
}

union_abstract_objectt::union_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_objectt(type, top, bottom)
{
  PRECONDITION(type.id() == ID_union);
}

union_abstract_objectt::union_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(expr, environment, ns)
{
  PRECONDITION(ns.follow(expr.type()).id() == ID_union);
}

abstract_object_pointert union_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return write_component(
    environment, ns, stack, to_member_expr(specifier), value, merging_write);
}

abstract_object_pointert union_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const member_exprt &member_expr,
  const namespacet &ns) const
{
  return environment.abstract_object_factory(
    member_expr.type(), ns, !is_bottom(), is_bottom());
}

abstract_object_pointert union_abstract_objectt::write_component(
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
    return std::make_shared<union_abstract_objectt>(type(), true, false);
  }
}
