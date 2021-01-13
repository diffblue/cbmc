/*******************************************************************\

Module: analyses variable-sensitivity interval-values arrays

Author: Diffblue Ltd.

\*******************************************************************/

#include "interval_array_abstract_object.h"
#include "abstract_environment.h"
#include "interval_abstract_value.h"
#include <util/interval.h>

interval_array_abstract_objectt::interval_array_abstract_objectt(typet type)
  : constant_array_abstract_objectt(type)
{
}

interval_array_abstract_objectt::interval_array_abstract_objectt(
  typet type,
  bool top,
  bool bottom)
  : constant_array_abstract_objectt(type, top, bottom)
{
}

interval_array_abstract_objectt::interval_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : constant_array_abstract_objectt(expr, environment, ns)
{
}

static constant_interval_exprt eval_and_get_as_interval(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  auto evaluated_index = environment.eval(expr, ns);
  auto evaluated_index_interval =
    std::dynamic_pointer_cast<const interval_abstract_valuet>(
      evaluated_index->unwrap_context());
  INVARIANT(
    evaluated_index_interval != nullptr,
    "Expecting expression to evaluate to index");
  return evaluated_index_interval->get_interval();
}

abstract_object_pointert interval_array_abstract_objectt::write_component(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  const index_exprt &index_expr = to_index_expr(expr);
  auto evaluated_index = environment.eval(index_expr.index(), ns);
  auto index_range =
    (std::dynamic_pointer_cast<const abstract_value_objectt>(
      evaluated_index->unwrap_context()))->index_range(ns);

  if (!index_range->advance_to_next())
    return make_top();

  sharing_ptrt<abstract_objectt> result = nullptr;
  do
  {
    auto array_after_write_at_index =
      constant_array_abstract_objectt::write_component(
        environment,
        ns,
        stack,
        index_exprt(index_expr.array(), index_range->current()),
        value,
        merging_write);
    bool dontcare;
    result = (result == nullptr)
               ? array_after_write_at_index
               : abstract_objectt::merge(result, array_after_write_at_index, dontcare);
  }
  while(!result->is_top() && index_range->advance_to_next());
  return result;
}

abstract_object_pointert interval_array_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const exprt &expr,
  const namespacet &ns) const
{
  const index_exprt &index_expr = to_index_expr(expr);
  auto evaluated_index = environment.eval(index_expr.index(), ns);
  auto index_range =
    (std::dynamic_pointer_cast<const abstract_value_objectt>(
      evaluated_index->unwrap_context()))->index_range(ns);

  if (!index_range->advance_to_next())
    return environment.abstract_object_factory(type().subtype(), ns);

  abstract_object_pointert value;
  do
  {
    auto value_at_index = constant_array_abstract_objectt::read_component(
      environment, index_exprt(index_expr.array(), index_range->current()), ns);

    bool dont_care;
    value = (value == nullptr)
      ? value_at_index
      : abstract_objectt::merge(value, value_at_index, dont_care);
  }
  while(!value->is_top() && index_range->advance_to_next());
  return value;
}

bool interval_array_abstract_objectt::eval_index(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index) const
{
  const index_exprt &index = to_index_expr(expr);
  auto index_interval = eval_and_get_as_interval(index.index(), env, ns);
  if(index_interval.is_single_value_interval())
  {
    out_index =
      numeric_cast_v<mp_integer>(to_constant_expr(index_interval.get_lower()));
    return true;
  }
  return false;
}

void interval_array_abstract_objectt::statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  constant_array_abstract_objectt::statistics(statistics, visited, env, ns);
  statistics.objects_memory_usage += memory_sizet::from_bytes(
    // the size we add by inheriting
    sizeof(*this) - sizeof(constant_array_abstract_objectt));
}
