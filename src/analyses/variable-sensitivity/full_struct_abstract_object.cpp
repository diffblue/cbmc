/*******************************************************************\

Module: Struct abstract object

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <util/std_expr.h>

#include "full_struct_abstract_object.h"
#include "location_update_visitor.h"
#include "map_visit.h"

// #define DEBUG

#ifdef DEBUG
#  include <iostream>
#endif

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const full_struct_abstract_objectt &ao)
  : abstract_aggregate_baset(ao), map(ao.map)
{
}

full_struct_abstract_objectt::full_struct_abstract_objectt(const typet &t)
  : abstract_aggregate_baset(t)
{
  PRECONDITION(t.id() == ID_struct);
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const typet &t,
  bool top,
  bool bottom)
  : abstract_aggregate_baset(t, top, bottom)
{
  PRECONDITION(t.id() == ID_struct);
  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

full_struct_abstract_objectt::full_struct_abstract_objectt(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_aggregate_baset(e, environment, ns)
{
  PRECONDITION(ns.follow(e.type()).id() == ID_struct);

  const struct_typet struct_type_def = to_struct_type(ns.follow(e.type()));

  bool did_initialize_values = false;
  auto struct_type_it = struct_type_def.components().begin();
  for(auto param_it = e.operands().begin(); param_it != e.operands().end();
      ++param_it, ++struct_type_it)
  {
    map.insert_or_replace(
      struct_type_it->get_name(),
      environment.abstract_object_factory(param_it->type(), *param_it, ns));
    did_initialize_values = true;
  }

  if(did_initialize_values)
  {
    set_not_top();
  }

  DATA_INVARIANT(verify(), "Structural invariants maintained");
}

abstract_object_pointert full_struct_abstract_objectt::read_component(
  const abstract_environmentt &environment,
  const exprt &expr,
  const namespacet &ns) const
{
#ifdef DEBUG
  std::cout << "Reading component " << to_member_expr(expr).get_component_name()
            << '\n';
#endif

  if(is_top())
  {
    return environment.abstract_object_factory(expr.type(), ns, true, false);
  }
  else
  {
    const member_exprt &member_expr = to_member_expr(expr);
    PRECONDITION(!is_bottom());

    const irep_idt c = member_expr.get_component_name();

    auto const value = map.find(c);

    if(value.has_value())
    {
      return value.value();
    }
    else
    {
      return environment.abstract_object_factory(
        member_expr.type(), ns, true, false);
    }
  }
}

abstract_object_pointert full_struct_abstract_objectt::write_component(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &expr,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  const member_exprt member_expr = to_member_expr(expr);
#ifdef DEBUG
  std::cout << "Writing component " << member_expr.get_component_name() << '\n';
#endif

  if(is_bottom())
  {
    return std::make_shared<full_struct_abstract_objectt>(
      member_expr.compound().type(), false, true);
  }

  const auto &result =
    std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

  if(!stack.empty())
  {
    abstract_object_pointert starting_value;
    const irep_idt c = member_expr.get_component_name();
    auto const old_value = map.find(c);
    if(!old_value.has_value())
    {
      starting_value = environment.abstract_object_factory(
        member_expr.type(), ns, true, false);
      result->map.insert(
        c, environment.write(starting_value, value, stack, ns, merging_write));
    }
    else
    {
      result->map.replace(
        c,
        environment.write(old_value.value(), value, stack, ns, merging_write));
    }

    result->set_not_top();
    DATA_INVARIANT(result->verify(), "Structural invariants maintained");
    return result;
  }
  else
  {
#ifdef DEBUG
    std::cout << "Setting component" << std::endl;
#endif

    const irep_idt c = member_expr.get_component_name();
    auto const old_value = result->map.find(c);

    if(merging_write)
    {
      if(is_top()) // struct is top
      {
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }

      INVARIANT(!result->map.empty(), "If not top, map cannot be empty");

      if(!old_value.has_value()) // component is top
      {
        DATA_INVARIANT(result->verify(), "Structural invariants maintained");
        return result;
      }

      result->map.replace(
        c,
        abstract_objectt::merge(old_value.value(), value, widen_modet::no)
          .object);
    }
    else
    {
      if(old_value.has_value())
      {
        result->map.replace(c, value);
      }
      else
      {
        result->map.insert(c, value);
      }
      result->set_not_top();
      INVARIANT(!result->is_bottom(), "top != bottom");
    }

    DATA_INVARIANT(result->verify(), "Structural invariants maintained");

    return result;
  }
}

void full_struct_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  // To ensure that a consistent ordering of fields is output, use
  // the underlying type declaration for this struct to determine
  // the ordering
  struct_union_typet type_decl = to_struct_union_type(ns.follow(type()));

  bool first = true;

  out << "{";
  for(const auto &field : type_decl.components())
  {
    auto value = map.find(field.get_name());
    if(value.has_value())
    {
      if(!first)
      {
        out << ", ";
      }
      out << '.' << field.get_name() << '=';
      static_cast<const abstract_object_pointert &>(value.value())
        ->output(out, ai, ns);
      first = false;
    }
  }
  out << "}";
}

bool full_struct_abstract_objectt::verify() const
{
  // Either the object is top or bottom (=> map empty)
  // or the map is not empty => neither top nor bottom
  return (is_top() || is_bottom()) == map.empty();
}

abstract_object_pointert full_struct_abstract_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  constant_struct_pointert cast_other =
    std::dynamic_pointer_cast<const full_struct_abstract_objectt>(other);
  if(cast_other)
    return merge_constant_structs(cast_other, widen_mode);

  return abstract_aggregate_baset::merge(other, widen_mode);
}

abstract_object_pointert full_struct_abstract_objectt::merge_constant_structs(
  constant_struct_pointert other,
  const widen_modet &widen_mode) const
{
  if(is_bottom())
    return std::make_shared<full_struct_abstract_objectt>(*other);

  const auto &result =
    std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

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

abstract_object_pointert full_struct_abstract_objectt::write_location_context(
  const locationt &location) const
{
  return visit_sub_elements(location_update_visitort(location));
}

abstract_object_pointert full_struct_abstract_objectt::merge_location_context(
  const locationt &location) const
{
  return visit_sub_elements(merge_location_update_visitort(location));
}

abstract_object_pointert full_struct_abstract_objectt::visit_sub_elements(
  const abstract_object_visitort &visitor) const
{
  const auto &result =
    std::dynamic_pointer_cast<full_struct_abstract_objectt>(mutable_clone());

  bool is_modified = visit_map(result->map, visitor);

  return is_modified ? result : shared_from_this();
}

exprt full_struct_abstract_objectt::to_predicate_internal(
  const exprt &name) const
{
  auto all_predicates = exprt::operandst{};

  for(auto field : map.get_sorted_view())
  {
    auto field_name = member_exprt(name, field.first, name.type());
    auto field_expr = field.second->to_predicate(field_name);

    if(!field_expr.is_true())
      all_predicates.push_back(field_expr);
  }

  if(all_predicates.empty())
    return true_exprt();
  if(all_predicates.size() == 1)
    return all_predicates.front();
  return and_exprt(all_predicates);
}

void full_struct_abstract_objectt::statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  shared_struct_mapt::viewt view;
  map.get_view(view);
  for(auto const &object : view)
  {
    if(visited.find(object.second) == visited.end())
    {
      object.second->get_statistics(statistics, visited, env, ns);
    }
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
