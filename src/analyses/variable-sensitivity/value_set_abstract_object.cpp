/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/two_value_array_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

class value_set_index_ranget : public index_ranget
{
public:
  typedef value_set_abstract_objectt::abstract_object_sett abstract_object_sett;
  explicit value_set_index_ranget(const abstract_object_sett &vals)
    : values(vals), cur(), next(values.begin())
  {
    PRECONDITION(!values.empty());
  }

  const exprt &current() const override
  {
    return cur;
  }
  bool advance_to_next() override
  {
    if(next == values.end())
      return false;

    cur = (*next)->to_constant();
    ++next;
    return true;
  }

private:
  const abstract_object_sett &values;
  exprt cur;
  abstract_object_sett::const_iterator next;
};

index_range_ptrt make_value_set_index_range(
  const value_set_abstract_objectt::abstract_object_sett &vals)
{
  return std::make_shared<value_set_index_ranget>(vals);
}

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type)
  : abstract_value_objectt(type), my_type(type_to_abstract_type(type))
{
  switch(my_type)
  {
  case abstract_typet::POINTER:
    values.insert(std::make_shared<constant_pointer_abstract_objectt>(type));
    break;
  case abstract_typet::CONSTANT:
    values.insert(std::make_shared<constant_abstract_valuet>(type));
    break;
  case abstract_typet::UNSUPPORTED:
    UNREACHABLE;
  }
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_value_objectt(type, top, bottom),
    my_type(type_to_abstract_type(type))
{
  switch(my_type)
  {
  case abstract_typet::POINTER:
    values.insert(
      std::make_shared<constant_pointer_abstract_objectt>(type, top, bottom));
    break;
  case abstract_typet::CONSTANT:
    values.insert(
      std::make_shared<constant_abstract_valuet>(type, top, bottom));
    break;
  case abstract_typet::UNSUPPORTED:
    UNREACHABLE;
  }
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(expr.type(), false, false),
    my_type(type_to_abstract_type(expr.type()))
{
  switch(my_type)
  {
  case abstract_typet::POINTER:
    values.insert(std::make_shared<constant_pointer_abstract_objectt>(
      expr, environment, ns));
    break;
  case abstract_typet::CONSTANT:
    values.insert(
      std::make_shared<constant_abstract_valuet>(expr, environment, ns));
    break;
  case abstract_typet::UNSUPPORTED:
    UNREACHABLE;
  }
  verify();
}

index_range_ptrt
value_set_abstract_objectt::index_range(const namespacet &ns) const
{
  if(values.empty())
    return make_indeterminate_index_range();

  return make_value_set_index_range(values);
}

abstract_object_pointert value_set_abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  std::size_t num_operands = expr.operands().size();
  PRECONDITION(operands.size() == num_operands);

  std::vector<abstract_object_sett> collective_operands;
  collective_operands.reserve(num_operands);
  for(const auto &op : operands)
  {
    auto vsab = std::dynamic_pointer_cast<const value_set_abstract_objectt>(
      maybe_unwrap_context(op));
    INVARIANT(vsab, "should be a value set abstract object");
    collective_operands.push_back(vsab->get_values());
  }

  abstract_object_sett resulting_objects;
  for_each_comb(
    collective_operands,
    [&resulting_objects, this, &expr, &environment, &ns](
      const std::vector<abstract_object_pointert> &ops) {
      auto operands_expr = exprt::operandst { };
      for (auto v : ops)
        operands_expr.push_back(v->to_constant());
      auto rewritten_expr = exprt(expr.id(), expr.type(), std::move(operands_expr));
      resulting_objects.insert(
        (*values.begin())->expression_transform(rewritten_expr, ops, environment, ns));
    });

  return resolve_new_values(resulting_objects);
}

abstract_object_pointert value_set_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  abstract_object_sett new_values;
  for(const auto &st_value : values)
  {
    new_values.insert(
      st_value->write(environment, ns, stack, specifier, value, merging_write));
  }
  return resolve_new_values(new_values);
}

abstract_object_pointert value_set_abstract_objectt::resolve_new_values(
  const abstract_object_sett &new_values) const
{
  PRECONDITION(!new_values.empty());

  if(new_values == values)
    return shared_from_this();

  abstract_object_sett unwrapped_values;
  for(auto const &value : new_values)
  {
    unwrapped_values.insert(
      maybe_extract_single_value(maybe_unwrap_context(value)));
  }

  abstract_typet new_type = get_type(*unwrapped_values.begin());
  if(
    unwrapped_values.size() > max_value_set_size &&
    new_type == abstract_typet::CONSTANT)
  {
    return to_interval(unwrapped_values);
  }
  if(unwrapped_values.size() == 1 && new_type == abstract_typet::UNSUPPORTED)
  {
    return (*unwrapped_values.begin());
  }

  const auto &result =
    std::dynamic_pointer_cast<value_set_abstract_objectt>(mutable_clone());

  if(
    unwrapped_values.size() > max_value_set_size ||
    new_type == abstract_typet::UNSUPPORTED)
  {
    result->set_top();
  }
  else
  {
    result->set_values(unwrapped_values);
  }
  return result;
}

abstract_object_pointert
value_set_abstract_objectt::merge(abstract_object_pointert other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const value_set_abstract_objectt>(other);
  if(cast_other && cast_other->get_my_type() == get_my_type())
  {
    auto union_values = values;
    union_values.insert(
      cast_other->get_values().begin(), cast_other->get_values().end());
    return resolve_new_values(union_values);
  }
  else
    return abstract_objectt::merge(other);
}

abstract_object_pointert value_set_abstract_objectt::to_interval(
  const abstract_object_sett &other_values) const
{
  PRECONDITION(!other_values.empty());
  if(get_type(*other_values.begin()) == abstract_typet::POINTER)
    return std::make_shared<constant_pointer_abstract_objectt>(
      type(), true, false);
  PRECONDITION(get_type(*other_values.begin()) == abstract_typet::CONSTANT);

  exprt lower_expr = (*other_values.begin())->to_constant();
  exprt upper_expr = (*other_values.begin())->to_constant();
  for(const auto &value : other_values)
  {
    const auto &value_expr = value->to_constant();
    lower_expr = constant_interval_exprt::get_min(lower_expr, value_expr);
    upper_expr = constant_interval_exprt::get_min(upper_expr, value_expr);
  }
  return std::make_shared<interval_abstract_valuet>(
    constant_interval_exprt(lower_expr, upper_expr));
}

bool value_set_abstract_objectt::verify() const
{
  CHECK_RETURN(my_type != abstract_typet::UNSUPPORTED);
  for(const auto &value : values)
  {
    CHECK_RETURN(
      !std::dynamic_pointer_cast<const context_abstract_objectt>(value));
    CHECK_RETURN(get_type(value) == my_type);
  }
  return true;
}

value_set_abstract_objectt::abstract_typet
value_set_abstract_objectt::get_type(const abstract_object_pointert &other)
{
  PRECONDITION(
    !std::dynamic_pointer_cast<const context_abstract_objectt>(other));
  PRECONDITION(!std::dynamic_pointer_cast<const abstract_aggregate_tag>(other));
  PRECONDITION(
    !std::dynamic_pointer_cast<const value_set_abstract_objectt>(other));

  if(std::dynamic_pointer_cast<const constant_pointer_abstract_objectt>(other))
    return abstract_typet::POINTER;
  if(std::dynamic_pointer_cast<const constant_abstract_valuet>(other))
    return abstract_typet::CONSTANT;
  UNREACHABLE;
  return abstract_typet::UNSUPPORTED;
}

void value_set_abstract_objectt::set_values(const abstract_object_sett &other_values)
{
  PRECONDITION(!other_values.empty());
  set_not_top();
  my_type = get_type(*other_values.begin());
  values = other_values;
  verify();
}

abstract_object_pointert value_set_abstract_objectt::maybe_extract_single_value(
  const abstract_object_pointert &maybe_singleton)
{
  auto const &value_as_set =
    std::dynamic_pointer_cast<const value_set_abstract_objectt>(
      maybe_singleton);
  if(value_as_set)
  {
    PRECONDITION(value_as_set->get_values().size() == 1);
    PRECONDITION(!std::dynamic_pointer_cast<const context_abstract_objectt>(
      *value_as_set->get_values().begin()));

    return *value_as_set->get_values().begin();
  }
  else
    return maybe_singleton;
}

abstract_object_pointert value_set_abstract_objectt::maybe_unwrap_context(
  const abstract_object_pointert &maybe_wrapped)
{
  auto const &context_value =
    std::dynamic_pointer_cast<const context_abstract_objectt>(maybe_wrapped);

  return context_value ? context_value->unwrap_context() : maybe_wrapped;
}

void value_set_abstract_objectt::output(
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
    for(auto const &value : values)
    {
      value->output(out, ai, ns);
      out << ", ";
    }
    out << ":value-set-end";
  }
}
