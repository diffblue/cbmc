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

index_range_ptrt make_value_set_index_range(const abstract_object_sett &vals)
{
  return std::make_shared<value_set_index_ranget>(vals);
}

exprt rewrite_expression(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &ops);

std::vector<abstract_object_sett>
unwrap_operands(const std::vector<abstract_object_pointert> &operands);

abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values);

/// Helper for converting singleton value sets into its only value.
/// \p maybe_singleton: either a set of abstract values or a single value
/// \return an abstract value without context
abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

/// Helper for converting context objects into its abstract-value children
/// \p maybe_wrapped: either an abstract value (or a set of those) or one
///   wrapped in a context
/// \return an abstract value without context (though it might be as set)
abstract_object_pointert
maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped);

/// Recursively construct a combination \p sub_con from \p super_con and once
///   constructed call \p f.
/// \param super_con: vector of some containers storing the values
/// \param sub_con: the one combination being currently constructed
/// \param f: callable with side-effects
template <typename Con, typename F>
void apply_comb(
  const std::vector<Con> &super_con,
  std::vector<typename Con::value_type> &sub_con,
  F f)
{
  size_t n = sub_con.size();
  if(n == super_con.size())
    f(sub_con);
  else
  {
    for(const auto &value : super_con[n])
    {
      sub_con.push_back(value);
      apply_comb(super_con, sub_con, f);
      sub_con.pop_back();
    }
  }
}

/// Call the function \p f on every combination of elements in \p super_con.
///   Hence the arity of \p f is `super_con.size()`. <{1,2},{1},{1,2,3}> ->
///   f(1,1,1), f(1,1,2), f(1,1,3), f(2,1,1), f(2,1,2), f(2,1,3).
/// \param super_con: vector of some containers storing the values
/// \param f: callable with side-effects
template <typename Con, typename F>
void for_each_comb(const std::vector<Con> &super_con, F f)
{
  std::vector<typename Con::value_type> sub_con;
  apply_comb(super_con, sub_con, f);
}

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type)
  : abstract_value_objectt(type)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_value_objectt(type, top, bottom)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type, top, bottom));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(expr.type(), false, false)
{
  values.insert(
    std::make_shared<constant_abstract_valuet>(expr, environment, ns));
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
  PRECONDITION(operands.size() == expr.operands().size());

  auto collective_operands = unwrap_operands(operands);

  if(expr.id() == ID_if)
    return evaluate_conditional(
      expr.type(), collective_operands, environment, ns);

  abstract_object_sett resulting_objects;

  auto dispatcher = values.first();
  for_each_comb(
    collective_operands,
    [&resulting_objects, &dispatcher, &expr, &environment, &ns](
      const std::vector<abstract_object_pointert> &ops) {
      auto rewritten_expr = rewrite_expression(expr, ops);
      resulting_objects.insert(
        dispatcher->expression_transform(rewritten_expr, ops, environment, ns));
    });

  return resolve_new_values(resulting_objects, environment);
}

abstract_object_pointert value_set_abstract_objectt::evaluate_conditional(
  const typet &type,
  const std::vector<abstract_object_sett> &operands,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  auto const condition = operands[0];

  auto const true_result = operands[1];
  auto const false_result = operands[2];

  auto all_true = true;
  auto all_false = true;
  for(auto v : condition)
  {
    auto expr = v->to_constant();
    all_true = all_true && expr.is_true();
    all_false = all_false && expr.is_false();
  }
  auto indeterminate = !all_true && !all_false;

  abstract_object_sett resulting_objects;
  if(all_true || indeterminate)
    resulting_objects.insert(true_result);
  if(all_false || indeterminate)
    resulting_objects.insert(false_result);
  return resolve_new_values(resulting_objects, env);
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
  return resolve_new_values(new_values, environment);
}

abstract_object_pointert value_set_abstract_objectt::resolve_new_values(
  const abstract_object_sett &new_values,
  const abstract_environmentt &environment) const
{
  auto result = resolve_values(new_values);
  return environment.add_object_context(result);
}

abstract_object_pointert value_set_abstract_objectt::resolve_values(
  const abstract_object_sett &new_values) const
{
  PRECONDITION(!new_values.empty());

  if(new_values == values)
    return shared_from_this();

  auto unwrapped_values = unwrap_and_extract_values(new_values);

  if(unwrapped_values.size() > max_value_set_size)
  {
    return to_interval(unwrapped_values);
  }
  //if(unwrapped_values.size() == 1)
  //{
  //  return (*unwrapped_values.begin());
  //}

  auto result =
    std::dynamic_pointer_cast<value_set_abstract_objectt>(mutable_clone());
  result->set_values(unwrapped_values);
  return result;
}

abstract_object_pointert
value_set_abstract_objectt::merge(abstract_object_pointert other) const
{
  auto other_value_set = std::dynamic_pointer_cast<const value_set_tag>(other);
  if(other_value_set)
  {
    auto union_values = values;
    union_values.insert(other_value_set->get_values());
    return resolve_values(union_values);
  }

  auto other_value =
    std::dynamic_pointer_cast<const constant_abstract_valuet>(other);
  if(other_value)
  {
    auto union_values = values;
    union_values.insert(other_value);
    return resolve_values(union_values);
  }

  return abstract_objectt::merge(other);
}

abstract_object_pointert value_set_abstract_objectt::to_interval(
  const abstract_object_sett &other_values) const
{
  PRECONDITION(!other_values.empty());

  exprt lower_expr = (*other_values.begin())->to_constant();
  exprt upper_expr = (*other_values.begin())->to_constant();
  for(const auto &value : other_values)
  {
    const auto &value_expr = value->to_constant();
    lower_expr = constant_interval_exprt::get_min(lower_expr, value_expr);
    upper_expr = constant_interval_exprt::get_max(upper_expr, value_expr);
  }
  return std::make_shared<interval_abstract_valuet>(
    constant_interval_exprt(lower_expr, upper_expr));
}

void value_set_abstract_objectt::set_values(
  const abstract_object_sett &other_values)
{
  PRECONDITION(!other_values.empty());
  set_not_top();
  values = other_values;
  verify();
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

    values.output(out, ai, ns);

    out << " :value-set-end";
  }
}

exprt rewrite_expression(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &ops)
{
  auto operands_expr = exprt::operandst{};
  for(auto v : ops)
    operands_expr.push_back(v->to_constant());
  auto rewritten_expr = exprt(expr.id(), expr.type(), std::move(operands_expr));
  return rewritten_expr;
}

std::vector<abstract_object_sett>
unwrap_operands(const std::vector<abstract_object_pointert> &operands)
{
  auto unwrapped = std::vector<abstract_object_sett>{};

  for(const auto &op : operands)
  {
    auto vsab =
      std::dynamic_pointer_cast<const value_set_tag>(maybe_unwrap_context(op));
    INVARIANT(vsab, "should be a value set abstract object");
    unwrapped.push_back(vsab->get_values());
  }

  return unwrapped;
}

abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values)
{
  abstract_object_sett unwrapped_values;
  for(auto const &value : values)
  {
    unwrapped_values.insert(
      maybe_extract_single_value(maybe_unwrap_context(value)));
  }

  return unwrapped_values;
}

abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton)
{
  auto const &value_as_set =
    std::dynamic_pointer_cast<const value_set_tag>(maybe_singleton);
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

abstract_object_pointert
maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped)
{
  auto const &context_value =
    std::dynamic_pointer_cast<const context_abstract_objectt>(maybe_wrapped);

  return context_value ? context_value->unwrap_context() : maybe_wrapped;
}
