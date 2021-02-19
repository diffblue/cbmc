/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <goto-programs/adjust_float_expressions.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/make_unique.h>
#include <util/simplify_expr.h>

class empty_index_ranget : public index_range_implementationt
{
public:
  const exprt &current() const override
  {
    return nil;
  }
  bool advance_to_next() override
  {
    return false;
  }
  index_range_implementation_ptrt reset() const override
  {
    return make_empty_index_range();
  }

private:
  exprt nil = nil_exprt();
};

class indeterminate_index_ranget : public single_value_index_ranget
{
public:
  indeterminate_index_ranget() : single_value_index_ranget(nil_exprt())
  {
  }

  index_range_implementation_ptrt reset() const override
  {
    return make_indeterminate_index_range();
  }
};

single_value_index_ranget::single_value_index_ranget(const exprt &val)
  : value(val), available(true)
{
}

const exprt &single_value_index_ranget::current() const
{
  return value;
}

bool single_value_index_ranget::advance_to_next()
{
  bool a = available;
  available = false;
  return a;
}

index_range_implementation_ptrt make_empty_index_range()
{
  return util_make_unique<empty_index_ranget>();
}

index_range_implementation_ptrt make_indeterminate_index_range()
{
  return util_make_unique<indeterminate_index_ranget>();
}

class single_value_value_ranget : public value_range_implementationt
{
public:
  explicit single_value_value_ranget(const abstract_object_pointert &val)
    : value(val), available(true)
  {
  }

  const abstract_object_pointert &current() const override
  {
    return value;
  }
  bool advance_to_next() override
  {
    bool a = available;
    available = false;
    return a;
  }
  value_range_implementation_ptrt reset() const override
  {
    return make_single_value_range(value);
  }

private:
  const abstract_object_pointert value;
  bool available;
};

value_range_implementation_ptrt
make_single_value_range(const abstract_object_pointert &value)
{
  return util_make_unique<single_value_value_ranget>(value);
}

static abstract_object_pointert constants_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns);
static abstract_object_pointert intervals_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns);
static abstract_object_pointert value_set_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns);

bool any_value_sets(const std::vector<abstract_object_pointert> &operands)
{
  return std::find_if(
           operands.begin(),
           operands.end(),
           [](const abstract_object_pointert &p) {
             return std::dynamic_pointer_cast<const value_set_abstract_objectt>(
                      p) != nullptr;
           }) != operands.end();
}

bool any_intervals(const std::vector<abstract_object_pointert> &operands)
{
  return std::find_if(
           operands.begin(),
           operands.end(),
           [](const abstract_object_pointert &p) {
             return std::dynamic_pointer_cast<const interval_abstract_valuet>(
                      p) != nullptr;
           }) != operands.end();
}

static abstract_object_pointert transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(any_value_sets(operands))
    return value_set_expression_transform(expr, operands, environment, ns);
  if(any_intervals(operands))
    return intervals_expression_transform(expr, operands, environment, ns);
  return constants_expression_transform(expr, operands, environment, ns);
}

abstract_object_pointert abstract_value_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return transform(expr, operands, environment, ns);
}

// constant_abstract_value expresion transfrom
static abstract_object_pointert try_transform_expr_with_all_rounding_modes(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns);

abstract_object_pointert constants_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  // try finding the rounding mode. If it's not constant, try
  // seeing if we can get the same result with all rounding modes
  auto rounding_mode_symbol =
    symbol_exprt(CPROVER_PREFIX "rounding_mode", signedbv_typet(32));
  auto rounding_mode_value = environment.eval(rounding_mode_symbol, ns);
  auto rounding_mode_constant = rounding_mode_value->to_constant();
  if(rounding_mode_constant.is_nil())
  {
    return try_transform_expr_with_all_rounding_modes(expr, environment, ns);
  }

  exprt adjusted_expr = expr;
  adjust_float_expressions(adjusted_expr, ns);
  exprt constant_replaced_expr = adjusted_expr;
  constant_replaced_expr.operands().clear();

  // Two passes over the expression - one for simplification,
  // another to check if there are any top subexpressions left
  for(const exprt &op : adjusted_expr.operands())
  {
    abstract_object_pointert lhs_abstract_object = environment.eval(op, ns);
    const exprt &lhs_value = lhs_abstract_object->to_constant();
    if(lhs_value.is_nil())
    {
      // do not give up if a sub-expression is not a constant,
      // because the whole expression may still be simplified in some cases
      constant_replaced_expr.operands().push_back(op);
    }
    else
    {
      // rebuild the operands list with constant versions of
      // any symbols
      constant_replaced_expr.operands().push_back(lhs_value);
    }
  }
  exprt simplified = simplify_expr(constant_replaced_expr, ns);

  for(const exprt &op : simplified.operands())
  {
    abstract_object_pointert lhs_abstract_object = environment.eval(op, ns);
    const exprt &lhs_value = lhs_abstract_object->to_constant();
    if(lhs_value.is_nil())
    {
      return environment.abstract_object_factory(
        simplified.type(), ns, true, false);
    }
  }

  return environment.abstract_object_factory(simplified.type(), simplified, ns);
}

static abstract_object_pointert try_transform_expr_with_all_rounding_modes(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  const symbol_exprt rounding_mode_symbol =
    symbol_exprt(CPROVER_PREFIX "rounding_mode", signedbv_typet(32));
  // NOLINTNEXTLINE (whitespace/braces)
  auto rounding_modes = std::array<ieee_floatt::rounding_modet, 4>{
    // NOLINTNEXTLINE (whitespace/braces)
    {ieee_floatt::ROUND_TO_EVEN,
     ieee_floatt::ROUND_TO_ZERO,
     ieee_floatt::ROUND_TO_MINUS_INF,
     // NOLINTNEXTLINE (whitespace/braces)
     ieee_floatt::ROUND_TO_PLUS_INF}};
  std::vector<abstract_object_pointert> possible_results;
  for(auto current_rounding_mode : rounding_modes)
  {
    abstract_environmentt child_env(environment);
    child_env.assign(
      rounding_mode_symbol,
      child_env.abstract_object_factory(
        signedbv_typet(32),
        from_integer(
          mp_integer(static_cast<unsigned long>(current_rounding_mode)),
          signedbv_typet(32)),
        ns),
      ns);

    // Dummy vector as the called expression_transform() ignores it
    std::vector<abstract_object_pointert> dummy;
    possible_results.push_back(
      constants_expression_transform(expr, dummy, child_env, ns));
  }
  auto first = possible_results.front()->to_constant();
  for(auto const &possible_result : possible_results)
  {
    auto current = possible_result->to_constant();
    if(current.is_nil() || current != first)
    {
      return environment.abstract_object_factory(expr.type(), ns, true, false);
    }
  }
  return possible_results.front();
}

///////////////////////////////////////////////////////
// intervals expression transform
using interval_abstract_value_pointert = sharing_ptrt<interval_abstract_valuet>;

static abstract_object_pointert interval_evaluate_conditional(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &env,
  const namespacet &ns);
static abstract_object_pointert interval_evaluate_unary_expr(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &environment,
  const namespacet &ns);

abstract_object_pointert intervals_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  std::size_t num_operands = expr.operands().size();
  PRECONDITION(operands.size() == num_operands);

  std::vector<sharing_ptrt<interval_abstract_valuet>> interval_operands;

  for(const auto &op : operands)
  {
    auto iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(op);
    if(!iav)
    {
      // The operand isn't an interval - if it's an integral constant we can
      // convert it into an interval.

      if(constant_interval_exprt::is_int(op->type()))
      {
        const auto op_as_constant = op->to_constant();
        if(op_as_constant.is_nil())
        {
          auto top_object =
            environment.abstract_object_factory(expr.type(), ns, true, false);
          auto top_context_object =
            std::dynamic_pointer_cast<const context_abstract_objectt>(
              top_object);
          CHECK_RETURN(top_context_object);
          return top_context_object->get_child();
        }
        const auto ivop =
          environment.abstract_object_factory(op->type(), op_as_constant, ns);
        const auto ivop_context =
          std::dynamic_pointer_cast<const context_abstract_objectt>(ivop);
        if(ivop_context)
        {
          iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(
            ivop_context->get_child());
        }
        else
          iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(ivop);
      }
      CHECK_RETURN(
        !std::dynamic_pointer_cast<const context_abstract_objectt>(iav));

      if(!iav)
      {
        // If we could not convert the operand into an interval,
        // e.g. if its type is not something we can represent as an interval,
        // try dispatching the expression_transform under that type instead.
        if(
          std::dynamic_pointer_cast<const constant_abstract_valuet>(op) !=
          nullptr)
          return constants_expression_transform(
            expr, operands, environment, ns);
        return op->expression_transform(expr, operands, environment, ns);
      }
    }

    INVARIANT(iav, "Should be an interval abstract value");
    interval_operands.push_back(iav);
  }

  if(num_operands == 0)
    return environment.abstract_object_factory(expr.type(), ns, true, false);

  if(expr.id() == ID_if)
    return interval_evaluate_conditional(
      expr, interval_operands, environment, ns);

  if(num_operands == 1)
    return interval_evaluate_unary_expr(
      expr, interval_operands, environment, ns);

  constant_interval_exprt result = interval_operands[0]->to_interval();

  for(size_t opIndex = 1; opIndex != interval_operands.size(); ++opIndex)
  {
    auto &interval_next = interval_operands[opIndex]->to_interval();
    result = result.eval(expr.id(), interval_next);
  }

  INVARIANT(
    result.type() == expr.type(),
    "Type of result interval should match expression type");
  return environment.abstract_object_factory(expr.type(), result, ns);
}

abstract_object_pointert interval_evaluate_conditional(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  auto const &condition_interval = interval_operands[0]->to_interval();
  auto const &true_interval = interval_operands[1]->to_interval();
  auto const &false_interval = interval_operands[2]->to_interval();

  auto condition_result = condition_interval.is_definitely_true();

  if(condition_result.is_unknown())
  {
    // Value of the condition is both true and false, so
    // combine the intervals of both the true and false expressions
    return env.abstract_object_factory(
      expr.type(),
      constant_interval_exprt(
        constant_interval_exprt::get_min(
          true_interval.get_lower(), false_interval.get_lower()),
        constant_interval_exprt::get_max(
          true_interval.get_upper(), false_interval.get_upper())),
      ns);
  }

  return condition_result.is_true()
           ? env.abstract_object_factory(
               true_interval.type(), true_interval, ns)
           : env.abstract_object_factory(
               false_interval.type(), false_interval, ns);
}

abstract_object_pointert interval_evaluate_unary_expr(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  const constant_interval_exprt &operand_expr =
    interval_operands[0]->to_interval();

  if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tce = to_typecast_expr(expr);

    const constant_interval_exprt &new_interval =
      operand_expr.typecast(tce.type());

    INVARIANT(
      new_interval.type() == expr.type(),
      "Type of result interval should match expression type");

    return environment.abstract_object_factory(tce.type(), new_interval, ns);
  }

  const constant_interval_exprt &interval_result = operand_expr.eval(expr.id());
  INVARIANT(
    interval_result.type() == expr.type(),
    "Type of result interval should match expression type");
  return environment.abstract_object_factory(expr.type(), interval_result, ns);
}

/////////////////////////////////////////////////////////
// value_set expression transform
static abstract_object_pointert value_set_evaluate_conditional(
  const typet &type,
  const std::vector<value_ranget> &operands,
  const abstract_environmentt &env,
  const namespacet &ns);

static std::vector<value_ranget>
unwrap_operands(const std::vector<abstract_object_pointert> &operands);

/// Helper for converting context objects into its abstract-value children
/// \p maybe_wrapped: either an abstract value (or a set of those) or one
///   wrapped in a context
/// \return an abstract value without context (though it might be as set)
static abstract_object_pointert
maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped);

static exprt rewrite_expression(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &ops);

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

static abstract_object_pointert resolve_new_values(
  const abstract_object_sett &new_values,
  const abstract_environmentt &environment);

static abstract_object_pointert
resolve_values(const abstract_object_sett &new_values);
static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values);
static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

static abstract_object_pointert value_set_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  PRECONDITION(operands.size() == expr.operands().size());

  auto collective_operands = unwrap_operands(operands);

  if(expr.id() == ID_if)
    return value_set_evaluate_conditional(
      expr.type(), collective_operands, environment, ns);

  abstract_object_sett resulting_objects;

  for_each_comb(
    collective_operands,
    [&resulting_objects, &expr, &environment, &ns](
      const std::vector<abstract_object_pointert> &ops) {
      auto rewritten_expr = rewrite_expression(expr, ops);
      resulting_objects.insert(transform(rewritten_expr, ops, environment, ns));
    });

  return resolve_new_values(resulting_objects, environment);
}

abstract_object_pointert value_set_evaluate_conditional(
  const typet &type,
  const std::vector<value_ranget> &operands,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  auto const &condition = operands[0];

  auto const &true_result = operands[1];
  auto const &false_result = operands[2];

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

static std::vector<value_ranget>
unwrap_operands(const std::vector<abstract_object_pointert> &operands)
{
  auto unwrapped = std::vector<value_ranget>{};

  for(const auto &op : operands)
  {
    auto av = std::dynamic_pointer_cast<const abstract_value_objectt>(
      maybe_unwrap_context(op));
    // INVARIANT(av, "should be an abstract value object");
    if(av)
      unwrapped.emplace_back(av->value_range());
    else // Forthcoming work will eliminate this line
      unwrapped.emplace_back(value_ranget{make_single_value_range(op)});
  }

  return unwrapped;
}

static exprt rewrite_expression(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &ops)
{
  auto operands_expr = exprt::operandst{};
  for(auto v : ops)
    operands_expr.push_back(v->to_constant());
  auto rewritten_expr = exprt(expr.id(), expr.type(), std::move(operands_expr));
  return rewritten_expr;
}

static abstract_object_pointert
maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped)
{
  auto const &context_value =
    std::dynamic_pointer_cast<const context_abstract_objectt>(maybe_wrapped);

  return context_value ? context_value->unwrap_context() : maybe_wrapped;
}

static abstract_object_sett
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

static abstract_object_pointert
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

static abstract_object_pointert resolve_new_values(
  const abstract_object_sett &new_values,
  const abstract_environmentt &environment)
{
  auto result = resolve_values(new_values);
  return environment.add_object_context(result);
}

static abstract_object_pointert
resolve_values(const abstract_object_sett &new_values)
{
  PRECONDITION(!new_values.empty());

  auto unwrapped_values = unwrap_and_extract_values(new_values);

  if(unwrapped_values.size() > value_set_abstract_objectt::max_value_set_size)
  {
    return unwrapped_values.to_interval();
  }
  //if(unwrapped_values.size() == 1)
  //{
  //  return (*unwrapped_values.begin());
  //}

  const auto &type = new_values.first()->type();
  auto result = std::make_shared<value_set_abstract_objectt>(type);
  result->set_values(unwrapped_values);
  return result;
}
