/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_configuration.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include "abstract_value_object.h"
#include "full_array_abstract_object.h"
#include "location_update_visitor.h"
#include "map_visit.h"

struct eval_index_resultt
{
  bool is_good;
  mp_integer value;
  bool overrun;
};

static eval_index_resultt eval_index(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns);
static eval_index_resultt eval_index(
  const mp_integer &index,
  const abstract_environmentt &env,
  const namespacet &ns);

template <typename index_fn>
abstract_object_pointert apply_to_index_range(
  const abstract_environmentt &environment,
  const exprt &expr,
  const namespacet &ns,
  index_fn &fn)
{
  const index_exprt &index_expr = to_index_expr(expr);
  auto evaluated_index = environment.eval(index_expr.index(), ns);
  auto index_range = (std::dynamic_pointer_cast<const abstract_value_objectt>(
                        evaluated_index->unwrap_context()))
                       ->index_range(ns);

  sharing_ptrt<abstract_objectt> result = nullptr;
  for(const auto &index : index_range)
  {
    auto at_index = fn(index_exprt(index_expr.array(), index));

    result =
      (result == nullptr)
        ? at_index
        : abstract_objectt::merge(result, at_index, widen_modet::no).object;

    if(result->is_top()) // no point in continuing once we've gone top
      break;
  }
  return result;
}

full_array_abstract_objectt::full_array_abstract_objectt(typet type)
  : abstract_aggregate_baset(type)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

full_array_abstract_objectt::full_array_abstract_objectt(
  typet type,
  bool top,
  bool bottom)
  : abstract_aggregate_baset(type, top, bottom)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

full_array_abstract_objectt::full_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_aggregate_baset(expr, environment, ns)
{
  if(expr.id() == ID_array)
  {
    mp_integer i = 0;
    for(const exprt &entry : expr.operands())
    {
      auto index = eval_index(i, environment, ns);
      map_put(index.value, environment.eval(entry, ns), index.overrun);
      ++i;
    }
    set_not_top();
  }
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

bool full_array_abstract_objectt::verify() const
{
  // Either the object is top or bottom (=> map empty)
  // or the map is not empty => neither top nor bottom
  return abstract_aggregate_baset::verify() &&
         (is_top() || is_bottom()) == map.empty();
}

void full_array_abstract_objectt::set_top_internal()
{
  // A structural invariant of constant_array_abstract_objectt is that
  // (is_top() || is_bottom()) => map.empty()
  map.clear();
}

abstract_object_pointert full_array_abstract_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const full_array_abstract_objectt>(other);
  if(cast_other)
    return full_array_merge(cast_other, widen_mode);

  return abstract_aggregate_baset::merge(other, widen_mode);
}

abstract_object_pointert full_array_abstract_objectt::full_array_merge(
  const full_array_pointert &other,
  const widen_modet &widen_mode) const
{
  if(is_bottom())
    return std::make_shared<full_array_abstract_objectt>(*other);

  const auto &result =
    std::dynamic_pointer_cast<full_array_abstract_objectt>(mutable_clone());

  bool modified = merge_shared_maps(map, other->map, result->map, widen_mode);
  if(!modified)
  {
    DATA_INVARIANT(verify(), "Structural invariants maintained");
    return shared_from_this();
  }
  else
  {
    INVARIANT(!result->is_top(), "Merge of maps will not generate top");
    INVARIANT(!result->is_bottom(), "Merge of maps will not generate bottom");
    DATA_INVARIANT(result->verify(), "Structural invariants maintained");
    return result;
  }
}

void full_array_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top() || is_bottom())
  {
    abstract_aggregate_baset::output(out, ai, ns);
  }
  else
  {
    out << "{";
    for(const auto &entry : map.get_sorted_view())
    {
      out << "[" << entry.first << "] = ";
      entry.second->output(out, ai, ns);
      out << "\n";
    }
    out << "}";
  }
}

abstract_object_pointert full_array_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const exprt &expr,
  const namespacet &ns) const
{
  if(is_top())
    return environment.abstract_object_factory(expr.type(), ns, true, false);

  auto read_element_fn =
    [this, &environment, &ns](const index_exprt &index_expr) {
      return this->read_element(environment, index_expr, ns);
    };

  auto result = apply_to_index_range(environment, expr, ns, read_element_fn);

  return (result != nullptr) ? result : get_top_entry(environment, ns);
}

abstract_object_pointert full_array_abstract_objectt::write_component(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  auto write_element_fn =
    [this, &environment, &ns, &stack, &value, &merging_write](
      const index_exprt &index_expr) {
      return this->write_element(
        environment, ns, stack, index_expr, value, merging_write);
    };

  auto result = apply_to_index_range(environment, expr, ns, write_element_fn);

  return (result != nullptr) ? result : make_top();
}

abstract_object_pointert full_array_abstract_objectt::read_element(
  const abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns) const
{
  PRECONDITION(!is_bottom());
  auto index = eval_index(expr, env, ns);

  if(index.is_good)
    return map_find_or_top(index.value, env, ns);

  // Although we don't know where we are reading from, and therefore
  // we should be returning a TOP value, we may still have useful
  // additional information in elements of the array - such as write
  // histories so we merge all the known array elements with TOP and return
  // that.

  // Create a new TOP value of the appropriate element type
  auto result = get_top_entry(env, ns);

  // Merge each known element into the TOP value
  for(const auto &element : map.get_view())
    result =
      abstract_objectt::merge(result, element.second, widen_modet::no).object;

  return result;
}

abstract_object_pointert full_array_abstract_objectt::write_element(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_bottom())
  {
    return abstract_aggregate_baset::write_component(
      environment, ns, stack, expr, value, merging_write);
  }

  if(!stack.empty())
    return write_sub_element(
      environment, ns, stack, expr, value, merging_write);

  return write_leaf_element(environment, ns, expr, value, merging_write);
}

abstract_object_pointert full_array_abstract_objectt::write_sub_element(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  const auto &result =
    std::dynamic_pointer_cast<full_array_abstract_objectt>(mutable_clone());

  auto index = eval_index(expr, environment, ns);

  if(index.is_good)
  {
    // We were able to evaluate the index to a value, which we
    // assume is in bounds...
    auto const existing_value = map_find_or_top(index.value, environment, ns);
    result->map_put(
      index.value,
      environment.write(existing_value, value, stack, ns, merging_write),
      index.overrun);
    result->set_not_top();
    DATA_INVARIANT(result->verify(), "Structural invariants maintained");
    return result;
  }
  else
  {
    // We were not able to evaluate the index to a value
    for(const auto &starting_value : map.get_view())
    {
      // Merging write since we don't know which index we are writing to
      result->map.replace(
        starting_value.first,
        environment.write(starting_value.second, value, stack, ns, true));

      result->set_not_top();
    }

    DATA_INVARIANT(result->verify(), "Structural invariants maintained");
    return result;
  }
}

abstract_object_pointert full_array_abstract_objectt::write_leaf_element(
  abstract_environmentt &environment,
  const namespacet &ns,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  const auto &result =
    std::dynamic_pointer_cast<full_array_abstract_objectt>(mutable_clone());

  auto index = eval_index(expr, environment, ns);

  if(index.is_good)
  {
    // We were able to evaluate the index expression to a constant
    if(merging_write)
    {
      if(is_top())
      {
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }

      INVARIANT(!result->map.empty(), "If not top, map cannot be empty");

      auto old_value = result->map.find(index.value);
      if(old_value.has_value()) // if not found it's top, so nothing to merge
      {
        result->map.replace(
          index.value,
          abstract_objectt::merge(old_value.value(), value, widen_modet::no)
            .object);
      }

      DATA_INVARIANT(result->verify(), "Structural invariants maintained");
      return result;
    }
    else
    {
      result->map_put(index.value, value, index.overrun);
      result->set_not_top();

      DATA_INVARIANT(result->verify(), "Structural invariants maintained");
      return result;
    }
  }

  // try to write to all
  // TODO(tkiley): Merge with each entry
  return abstract_aggregate_baset::write_component(
    environment, ns, std::stack<exprt>(), expr, value, merging_write);
}

void full_array_abstract_objectt::map_put(
  mp_integer index_value,
  const abstract_object_pointert &value,
  bool overrun)
{
  auto old_value = map.find(index_value);

  if(!old_value.has_value())
    map.insert(index_value, value);
  else
  {
    // if we're over the max_index, merge with existing value
    auto replacement_value =
      overrun
        ? abstract_objectt::merge(old_value.value(), value, widen_modet::no)
            .object
        : value;

    map.replace(index_value, replacement_value);
  }
}

abstract_object_pointert full_array_abstract_objectt::map_find_or_top(
  mp_integer index_value,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  auto value = map.find(index_value);
  if(value.has_value())
    return value.value();
  return get_top_entry(env, ns);
}

abstract_object_pointert full_array_abstract_objectt::get_top_entry(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  return env.abstract_object_factory(type().subtype(), ns, true, false);
}

abstract_object_pointert full_array_abstract_objectt::write_location_context(
  const locationt &location) const
{
  return visit_sub_elements(location_update_visitort(location));
}

abstract_object_pointert full_array_abstract_objectt::merge_location_context(
  const locationt &location) const
{
  return visit_sub_elements(merge_location_update_visitort(location));
}

abstract_object_pointert full_array_abstract_objectt::visit_sub_elements(
  const abstract_object_visitort &visitor) const
{
  const auto &result =
    std::dynamic_pointer_cast<full_array_abstract_objectt>(mutable_clone());

  bool is_modified = visit_map(result->map, visitor);

  return is_modified ? result : shared_from_this();
}

exprt full_array_abstract_objectt::to_predicate_internal(
  const exprt &name) const
{
  auto all_predicates = exprt::operandst{};

  for(auto field : map.get_sorted_view())
  {
    auto ii = from_integer(field.first.to_long(), integer_typet());
    auto index = index_exprt(name, ii);
    auto field_expr = field.second->to_predicate(index);

    if(!field_expr.is_true())
      all_predicates.push_back(field_expr);
  }

  if(all_predicates.empty())
    return true_exprt();
  if(all_predicates.size() == 1)
    return all_predicates.front();
  return and_exprt(all_predicates);
}

void full_array_abstract_objectt::statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  for(const auto &object : map.get_view())
  {
    if(visited.find(object.second) == visited.end())
    {
      object.second->get_statistics(statistics, visited, env, ns);
    }
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}

static eval_index_resultt eval_index(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  const auto &index_expr = to_index_expr(expr);
  auto index_abstract_object = env.eval(index_expr.index(), ns);
  auto value = index_abstract_object->to_constant();

  if(!value.is_constant())
    return {false};

  mp_integer out_index;
  bool result = to_integer(to_constant_expr(value), out_index);
  if(result)
    return {false};

  return eval_index(out_index, env, ns);
}

static eval_index_resultt eval_index(
  const mp_integer &index,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  auto max_array_index = env.configuration().maximum_array_index;
  bool overrun = (index >= max_array_index);

  return {true, overrun ? max_array_index : index, overrun};
}
