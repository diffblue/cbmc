/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_pointer_object.h>

#include <util/pointer_expr.h>

#include "abstract_object_statistics.h"

abstract_pointer_objectt::abstract_pointer_objectt(const typet &t)
  : abstract_objectt(t)
{
  PRECONDITION(t.id() == ID_pointer);
}

abstract_pointer_objectt::abstract_pointer_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_objectt(type, top, bottom)
{
  PRECONDITION(type.id() == ID_pointer);
}

abstract_pointer_objectt::abstract_pointer_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(e, environment, ns)
{
  PRECONDITION(e.type().id() == ID_pointer);
}

static bool is_dereference(const exprt &expr);
static bool is_typecast_from_void_ptr(const exprt &expr);

abstract_object_pointert abstract_pointer_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(is_dereference(expr))
    return read_dereference(environment, ns);

  if(is_typecast_from_void_ptr(expr))
    return typecast_from_void_ptr(expr, operands, environment, ns);

  if(is_ptr_diff(expr))
    return eval_ptr_diff(expr, operands, environment, ns);

  if(is_ptr_comparison(expr))
    return eval_ptr_comparison(expr, operands, environment, ns);

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert abstract_pointer_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return write_dereference(environment, ns, stack, value, merging_write);
}

void abstract_pointer_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_pointers;
}

abstract_object_pointert abstract_pointer_objectt::typecast_from_void_ptr(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto pointer =
    std::dynamic_pointer_cast<const abstract_pointer_objectt>(operands.front());
  if(pointer)
    return pointer->typecast(expr.type(), environment, ns);

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert abstract_pointer_objectt::eval_ptr_diff(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(is_top() || operands[1]->is_top())
    return environment.eval(nil_exprt(), ns);

  return ptr_diff(expr, operands, environment, ns);
}

abstract_object_pointert abstract_pointer_objectt::eval_ptr_comparison(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto result = ptr_comparison_expr(expr, operands, environment, ns);
  return environment.eval(result, ns);
}

static bool is_dereference(const exprt &expr)
{
  return expr.id() == ID_dereference;
}

static bool is_typecast_from_void_ptr(const exprt &expr)
{
  if(expr.id() != ID_typecast)
    return false;

  const typecast_exprt &tce = to_typecast_expr(expr);
  return tce.op().id() == ID_symbol && is_void_pointer(tce.op().type());
}
