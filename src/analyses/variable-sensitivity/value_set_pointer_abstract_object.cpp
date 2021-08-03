/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Value Set of Pointer Abstract Object

#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_pointer_abstract_object.h>
#include <numeric>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>

#include "abstract_environment.h"

static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values);

/// Helper for converting singleton value sets into its only value.
/// \p maybe_singleton: either a set of abstract values or a single value
/// \return an abstract value without context
static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const typet &type)
  : abstract_pointer_objectt(type)
{
  values.insert(std::make_shared<constant_pointer_abstract_objectt>(type));
}

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const typet &new_type,
  bool top,
  bool bottom,
  const abstract_object_sett &new_values)
  : abstract_pointer_objectt(new_type, top, bottom), values(new_values)
{
}

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_pointer_objectt(type, top, bottom)
{
  values.insert(
    std::make_shared<constant_pointer_abstract_objectt>(type, top, bottom));
}

value_set_pointer_abstract_objectt::value_set_pointer_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_pointer_objectt(expr.type(), false, false)
{
  values.insert(
    std::make_shared<constant_pointer_abstract_objectt>(expr, environment, ns));
}

abstract_object_pointert value_set_pointer_abstract_objectt::read_dereference(
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  if(is_top() || is_bottom())
  {
    return env.abstract_object_factory(
      type().subtype(), ns, is_top(), !is_top());
  }

  abstract_object_sett results;
  for(auto value : values)
  {
    auto pointer =
      std::dynamic_pointer_cast<const abstract_pointer_objectt>(value);
    results.insert(pointer->read_dereference(env, ns));
  }

  return results.first();
}

abstract_object_pointert value_set_pointer_abstract_objectt::write_dereference(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const abstract_object_pointert &new_value,
  bool merging_write) const
{
  if(is_top() || is_bottom())
  {
    environment.havoc("Writing to a 2value pointer");
    return shared_from_this();
  }

  for(auto value : values)
  {
    auto pointer =
      std::dynamic_pointer_cast<const abstract_pointer_objectt>(value);
    pointer->write_dereference(
      environment, ns, stack, new_value, merging_write);
  }

  return shared_from_this();
}

abstract_object_pointert value_set_pointer_abstract_objectt::typecast(
  const typet &new_type,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  INVARIANT(is_void_pointer(type()), "Only allow pointer casting from void*");
  abstract_object_sett new_values;
  for(auto value : values)
  {
    if(value->is_top()) // multiple mallocs in the same scope can cause spurious
      continue; // TOP values, which we can safely strip out during the cast

    auto pointer =
      std::dynamic_pointer_cast<const abstract_pointer_objectt>(value);
    new_values.insert(pointer->typecast(new_type, environment, ns));
  }
  return std::make_shared<value_set_pointer_abstract_objectt>(
    new_type, is_top(), is_bottom(), new_values);
}

abstract_object_pointert value_set_pointer_abstract_objectt::ptr_diff(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto rhs =
    std::dynamic_pointer_cast<const value_set_pointer_abstract_objectt>(
      operands.back());

  auto differences = std::vector<abstract_object_pointert>{};

  for(auto &lhsv : values)
  {
    auto lhsp = std::dynamic_pointer_cast<const abstract_pointer_objectt>(lhsv);
    for(auto const &rhsp : rhs->values)
    {
      auto ops = std::vector<abstract_object_pointert>{lhsp, rhsp};
      differences.push_back(lhsp->ptr_diff(expr, ops, environment, ns));
    }
  }

  return std::accumulate(
    differences.cbegin(),
    differences.cend(),
    differences.front(),
    [](
      const abstract_object_pointert &lhs,
      const abstract_object_pointert &rhs) {
      return abstract_objectt::merge(lhs, rhs, widen_modet::no).object;
    });
}

exprt value_set_pointer_abstract_objectt::ptr_comparison_expr(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  auto rhs =
    std::dynamic_pointer_cast<const value_set_pointer_abstract_objectt>(
      operands.back());

  auto comparisons = std::set<exprt>{};

  for(auto &lhsv : values)
  {
    auto lhsp = std::dynamic_pointer_cast<const abstract_pointer_objectt>(lhsv);
    for(auto const &rhsp : rhs->values)
    {
      auto ops = std::vector<abstract_object_pointert>{lhsp, rhsp};
      auto comparison = lhsp->ptr_comparison_expr(expr, ops, environment, ns);
      auto result = simplify_expr(comparison, ns);
      comparisons.insert(result);
    }
  }

  if(comparisons.size() > 1)
    return nil_exprt();
  return *comparisons.cbegin();
}

abstract_object_pointert value_set_pointer_abstract_objectt::resolve_values(
  const abstract_object_sett &new_values) const
{
  PRECONDITION(!new_values.empty());

  if(new_values == values)
    return shared_from_this();

  auto unwrapped_values = unwrap_and_extract_values(new_values);

  auto result = std::dynamic_pointer_cast<value_set_pointer_abstract_objectt>(
    mutable_clone());

  if(unwrapped_values.size() > max_value_set_size)
  {
    result->set_top();
  }
  else
  {
    result->set_values(unwrapped_values);
  }
  return result;
}

abstract_object_pointert value_set_pointer_abstract_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other = std::dynamic_pointer_cast<const value_set_tag>(other);
  if(cast_other)
  {
    auto union_values = values;
    union_values.insert(cast_other->get_values());
    return resolve_values(union_values);
  }

  return abstract_objectt::merge(other, widen_mode);
}

void value_set_pointer_abstract_objectt::set_values(
  const abstract_object_sett &other_values)
{
  PRECONDITION(!other_values.empty());
  set_not_top();
  values = other_values;
}

void value_set_pointer_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top())
  {
    out << "TOP";
  }
  else if(is_bottom())
  {
    out << "BOTTOM";
  }
  else
  {
    out << "value-set-begin: ";

    values.output(out, ai, ns);

    out << " :value-set-end";
  }
}

abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values)
{
  abstract_object_sett unwrapped_values;
  for(auto const &value : values)
  {
    unwrapped_values.insert(maybe_extract_single_value(value));
  }

  return unwrapped_values;
}

abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton)
{
  auto const &value_as_set = std::dynamic_pointer_cast<const value_set_tag>(
    maybe_singleton->unwrap_context());
  if(value_as_set)
  {
    PRECONDITION(value_as_set->get_values().size() == 1);
    PRECONDITION(!std::dynamic_pointer_cast<const context_abstract_objectt>(
      value_as_set->get_values().first()));

    return value_as_set->get_values().first();
  }
  else
    return maybe_singleton;
}
