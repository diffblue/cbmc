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
    return eval_typecast_from_void_ptr(expr, operands, environment, ns);

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

abstract_object_pointert abstract_pointer_objectt::read_dereference(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  pointer_typet pointer_type(to_pointer_type(type()));
  const typet &pointed_to_type = pointer_type.subtype();

  return env.abstract_object_factory(pointed_to_type, ns, true, false);
}

abstract_object_pointert abstract_pointer_objectt::write_dereference(
  abstract_environmentt &env,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    env.havoc("Writing to a 2value pointer");
    return shared_from_this();
  }

  return std::make_shared<abstract_pointer_objectt>(type(), true, false);
}

abstract_object_pointert abstract_pointer_objectt::typecast(
  const typet &new_type,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  INVARIANT(is_void_pointer(type()), "Only allow pointer casting from void*");
  return std::make_shared<abstract_pointer_objectt>(
    new_type, is_top(), is_bottom());
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

abstract_object_pointert abstract_pointer_objectt::eval_typecast_from_void_ptr(
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
  auto &rhs = operands.back();

  if(same_target(rhs))
    return environment.eval(offset_from(rhs), ns);

  return abstract_objectt::expression_transform(
    expr, operands, environment, ns);
}

abstract_object_pointert abstract_pointer_objectt::eval_ptr_comparison(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto result = ptr_comparison_expr(expr, operands, environment, ns);
  return environment.eval(result, ns)->unwrap_context();
}

exprt abstract_pointer_objectt::ptr_comparison_expr(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(expr.id() == ID_not)
  {
    auto const &not_expr = to_not_expr(expr);
    auto result = simplify_vsd_expr(
      ptr_comparison_expr(not_expr.op(), operands, environment, ns), ns);
    return invert_result(result);
  }

  auto rhs =
    std::dynamic_pointer_cast<const abstract_pointer_objectt>(operands.back());

  if(same_target(rhs)) // rewrite in terms of pointer offset
  {
    auto lhs_offset = offset();
    auto rhs_offset = rhs->offset();
    return binary_relation_exprt(offset(), expr.id(), rhs->offset());
  }

  // not same target, can only eval == and !=
  auto eval_obj =
    environment.abstract_object_factory(expr.type(), ns, true, false)
      ->unwrap_context();
  return eval_obj->expression_transform(expr, operands, environment, ns)
    ->to_constant();
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
