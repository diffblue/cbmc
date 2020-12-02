/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <ostream>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "constant_array_abstract_object.h"

constant_array_abstract_objectt::constant_array_abstract_objectt(typet type)
  : array_abstract_objectt(type)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

constant_array_abstract_objectt::constant_array_abstract_objectt(
  typet type,
  bool top,
  bool bottom)
  : array_abstract_objectt(type, top, bottom)
{
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

constant_array_abstract_objectt::constant_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : array_abstract_objectt(expr, environment, ns)
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

bool constant_array_abstract_objectt::verify() const
{
  // Either the object is top or bottom (=> map empty)
  // or the map is not empty => neither top nor bottom
  return array_abstract_objectt::verify() &&
         (is_top() || is_bottom()) == map.empty();
}

void constant_array_abstract_objectt::set_top_internal()
{
  // A structural invariant of constant_array_abstract_objectt is that
  // (is_top() || is_bottom()) => map.empty()
  map.clear();
}

abstract_object_pointert
constant_array_abstract_objectt::merge(abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const constant_array_abstract_objectt>(other);
  if(cast_other)
  {
    return constant_array_merge(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return array_abstract_objectt::merge(other);
  }
}

abstract_object_pointert constant_array_abstract_objectt::constant_array_merge(
  const constant_array_pointert other) const
{
  if(is_bottom())
  {
    return std::make_shared<constant_array_abstract_objectt>(*other);
  }
  else
  {
    const auto &result =
      std::dynamic_pointer_cast<constant_array_abstract_objectt>(
        mutable_clone());

    bool modified =
      abstract_objectt::merge_shared_maps<mp_integer, mp_integer_hasht>(
        map, other->map, result->map);

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
}

void constant_array_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top() || is_bottom())
  {
    array_abstract_objectt::output(out, ai, ns);
  }
  else
  {
    shared_array_mapt::sorted_viewt view;
    map.get_view(view);

    out << "{";
    for(const auto &entry : view)
    {
      out << "[" << entry.first << "] = ";
      entry.second->output(out, ai, ns);
      out << "\n";
    }
    out << "}";
  }
}

abstract_object_pointert constant_array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet &ns) const
{
  if(is_top())
  {
    return env.abstract_object_factory(index.type(), ns, true);
  }
  else
  {
    PRECONDITION(!is_bottom());
    mp_integer index_value;
    if(eval_index(index, env, ns, index_value))
    {
      auto const value = map.find(index_value);

      // Here we are assuming it is always in bounds
      if(!value.has_value())
      {
        return env.abstract_object_factory(type().subtype(), ns, true, false);
      }
      else
      {
        return value.value();
      }
    }
    else
    {
      // Although we don't know where we are reading from, and therefore
      // we should be returning a TOP value, we may still have useful
      // additional information in elements of the array - such as write
      // histories so we merge all the known array elements with TOP and return
      // that.

      // Create a new TOP value of the appropriate element type
      abstract_object_pointert result =
        env.abstract_object_factory(type().subtype(), ns, true, false);

      // Merge each known element into the TOP value
      shared_array_mapt::viewt known_elements;
      map.get_view(known_elements);
      bool dummy;
      for(const auto &element : known_elements)
      {
        result = abstract_objectt::merge(result, element.second, dummy);
      }

      return result;
    }
  }
}

abstract_object_pointert constant_array_abstract_objectt::write_index(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const index_exprt &index_expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  if(is_bottom())
  {
    return array_abstract_objectt::write_index(
      environment, ns, stack, index_expr, value, merging_write);
  }

  const auto &result =
    std::dynamic_pointer_cast<constant_array_abstract_objectt>(mutable_clone());

  if(!stack.empty())
  {
    mp_integer index_value;
    if(eval_index(index_expr, environment, ns, index_value))
    {
      // We were able to evaluate the index to a value, which we
      // assume is in bounds...
      auto const old_value = map.find(index_value);

      if(!old_value.has_value())
      {
        result->map.insert(
          index_value,
          environment.write(
            get_top_entry(environment, ns), value, stack, ns, merging_write));
      }
      else
      {
        result->map.replace(
          index_value,
          environment.write(
            old_value.value(), value, stack, ns, merging_write));
      }

      result->set_not_top();
      DATA_INVARIANT(result->verify(), "Structural invariants maintained");
      return result;
    }
    else
    {
      // We were not able to evaluate the index to a value
      shared_array_mapt::viewt view;
      map.get_view(view);

      for(const auto &starting_value : view)
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
  else
  {
    mp_integer index_value;

    if(eval_index(index_expr, environment, ns, index_value))
    {
      // We were able to evalute the index expression to a constant
      if(merging_write)
      {
        if(is_top())
        {
          DATA_INVARIANT(result->verify(), "Structural invariants maintained");
          return result;
        }

        INVARIANT(!result->map.empty(), "If not top, map cannot be empty");

        auto const old_value = result->map.find(index_value);

        if(!old_value.has_value()) // Array element is top
        {
          DATA_INVARIANT(result->verify(), "Structural invariants maintained");
          return result;
        }

        bool dummy;

        result->map.replace(
          index_value,
          abstract_objectt::merge(old_value.value(), value, dummy));

        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }
      else
      {
        auto const old_value = result->map.find(index_value);
        if(old_value.has_value())
        {
          if(value != abstract_object_pointert{old_value.value()})
          {
            result->map.replace(index_value, value);
          }
        }
        else
        {
          result->map.insert(index_value, value);
        }
        result->set_not_top();
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }
    }

    // try to write to all
    // TODO(tkiley): Merge with each entry
    return array_abstract_objectt::write_index(
      environment, ns, stack, index_expr, value, merging_write);
  }
}

abstract_object_pointert constant_array_abstract_objectt::get_top_entry(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  return env.abstract_object_factory(type().subtype(), ns, true, false);
}

bool constant_array_abstract_objectt::eval_index(
  const index_exprt &index,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index) const
{
  abstract_object_pointert index_abstract_object = env.eval(index.index(), ns);
  exprt value = index_abstract_object->to_constant();
  if(value.is_constant())
  {
    constant_exprt constant_index = to_constant_expr(value);
    bool result = to_integer(constant_index, out_index);
    return !result;
  }
  else
  {
    return false;
  }
}

abstract_object_pointert constant_array_abstract_objectt::visit_sub_elements(
  const abstract_object_visitort &visitor) const
{
  const auto &result =
    std::dynamic_pointer_cast<constant_array_abstract_objectt>(mutable_clone());

  bool modified = false;

  shared_array_mapt::viewt view;
  result->map.get_view(view);

  for(auto &item : view)
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

void constant_array_abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  array_abstract_objectt::get_statistics(statistics, visited, env, ns);
  shared_array_mapt::viewt view;
  map.get_view(view);
  for(const auto &object : view)
  {
    if(visited.find(object.second) == visited.end())
    {
      object.second->get_statistics(statistics, visited, env, ns);
    }
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
