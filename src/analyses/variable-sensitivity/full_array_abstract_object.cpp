/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>

#include "abstract_value_object.h"
#include "full_array_abstract_object.h"

bool eval_index(
  const exprt &index,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index);

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
    int index = 0;
    for(const exprt &entry : expr.operands())
    {
      map.insert(mp_integer(index), environment.eval(entry, ns));
      ++index;
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
  mp_integer index_value;
  if(eval_index(expr, env, ns, index_value))
  {
    // Here we are assuming it is always in bounds
    auto const value = map.find(index_value);
    if(value.has_value())
      return value.value();
    return get_top_entry(env, ns);
  }
  else
  {
    // Although we don't know where we are reading from, and therefore
    // we should be returning a TOP value, we may still have useful
    // additional information in elements of the array - such as write
    // histories so we merge all the known array elements with TOP and return
    // that.

    // Create a new TOP value of the appropriate element type
    abstract_object_pointert result = get_top_entry(env, ns);

    // Merge each known element into the TOP value
    for(const auto &element : map.get_view())
      result =
        abstract_objectt::merge(result, element.second, widen_modet::no).object;

    return result;
  }
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

  mp_integer index_value;
  bool good_index = eval_index(expr, environment, ns, index_value);

  if(good_index)
  {
    // We were able to evaluate the index to a value, which we
    // assume is in bounds...
    auto const old_value = map.find(index_value);

    if(old_value.has_value())
    {
      result->map.replace(
        index_value,
        environment.write(old_value.value(), value, stack, ns, merging_write));
    }
    else
    {
      result->map.insert(
        index_value,
        environment.write(
          get_top_entry(environment, ns), value, stack, ns, merging_write));
    }

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

  mp_integer index_value;
  bool good_index = eval_index(expr, environment, ns, index_value);

  if(good_index)
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

      auto old_value = result->map.find(index_value);
      if(old_value.has_value()) // if not found it's top, so nothing to merge
      {
        result->map.replace(
          index_value,
          abstract_objectt::merge(old_value.value(), value, widen_modet::no)
            .object);
      }

      DATA_INVARIANT(result->verify(), "Structural invariants maintained");
      return result;
    }
    else
    {
      auto old_value = result->map.find(index_value);

      if(old_value.has_value())
        result->map.replace(index_value, value);
      else
        result->map.insert(index_value, value);

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

abstract_object_pointert full_array_abstract_objectt::get_top_entry(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  return env.abstract_object_factory(type().subtype(), ns, true, false);
}

abstract_object_pointert full_array_abstract_objectt::visit_sub_elements(
  const abstract_object_visitort &visitor) const
{
  const auto &result =
    std::dynamic_pointer_cast<full_array_abstract_objectt>(mutable_clone());

  bool modified = false;
  for(auto &item : result->map.get_view())
  {
    auto newval = visitor.visit(item.second);
    if(newval != item.second)
    {
      result->map.replace(item.first, std::move(newval));
      modified = true;
    }
  }

  if(modified)
  {
    return result;
  }
  else
  {
    return shared_from_this();
  }
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

bool eval_index(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index)
{
  const index_exprt &index = to_index_expr(expr);
  abstract_object_pointert index_abstract_object = env.eval(index.index(), ns);
  exprt value = index_abstract_object->to_constant();

  if(!value.is_constant())
    return false;

  constant_exprt constant_index = to_constant_expr(value);
  bool result = to_integer(constant_index, out_index);
  return !result;
}
