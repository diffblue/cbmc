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

// constant_abstract_value expression transfrom
class constants_evaluator
{
public:
  constants_evaluator(
    const exprt &e,
    const abstract_environmentt &env,
    const namespacet &n)
    : expression(e), environment(env), ns(n)
  {
  }

  abstract_object_pointert operator()() const
  {
    // try finding the rounding mode. If it's not constant, try
    // seeing if we can get the same result with all rounding modes
    if(rounding_mode_is_not_set())
      return try_transform_expr_with_all_rounding_modes();

    return transform();
  }

private:
  abstract_object_pointert transform() const
  {
    exprt expr = adjust_expression_for_rounding_mode();
    auto operands = expr.operands();
    expr.operands().clear();

    // Two passes over the expression - one for simplification,
    // another to check if there are any top subexpressions left
    for(const exprt &op : operands)
    {
      auto lhs_value = eval_constant(op);

      // do not give up if a sub-expression is not a constant,
      // because the whole expression may still be simplified in some cases
      expr.operands().push_back(lhs_value.is_nil() ? op : lhs_value);
    }

    exprt simplified = simplify_expr(expr, ns);
    for(const exprt &op : simplified.operands())
    {
      auto lhs_value = eval_constant(op);
      if(lhs_value.is_nil())
        return top(simplified.type());
    }

    // the expression is fully simplified
    return environment.abstract_object_factory(
      simplified.type(), simplified, ns);
  }

  abstract_object_pointert try_transform_expr_with_all_rounding_modes() const
  {
    std::vector<abstract_object_pointert> possible_results;
    for(auto rounding_mode : all_rounding_modes)
    {
      auto child_env(environment_with_rounding_mode(rounding_mode));
      possible_results.push_back(
        constants_evaluator(expression, child_env, ns)());
    }

    auto first = possible_results.front()->to_constant();
    for(auto const &possible_result : possible_results)
    {
      auto current = possible_result->to_constant();
      if(current.is_nil() || current != first)
        return top(expression.type());
    }
    return possible_results.front();
  }

  abstract_environmentt
  environment_with_rounding_mode(ieee_floatt::rounding_modet rm) const
  {
    abstract_environmentt child_env(environment);
    child_env.assign(
      rounding_mode_symbol,
      child_env.abstract_object_factory(
        signedbv_typet(32),
        from_integer(
          mp_integer(static_cast<unsigned long>(rm)), signedbv_typet(32)),
        ns),
      ns);
    return child_env;
  }

  exprt adjust_expression_for_rounding_mode() const
  {
    exprt adjusted_expr = expression;
    adjust_float_expressions(adjusted_expr, ns);
    return adjusted_expr;
  }

  exprt eval_constant(const exprt &op) const
  {
    return environment.eval(op, ns)->to_constant();
  }

  abstract_object_pointert top(const typet &type) const
  {
    return environment.abstract_object_factory(type, ns, true, false);
  }

  bool rounding_mode_is_not_set() const
  {
    auto rounding_mode = eval_constant(rounding_mode_symbol);
    return rounding_mode.is_nil();
  }

  const exprt &expression;
  const abstract_environmentt &environment;
  const namespacet &ns;

  static const symbol_exprt rounding_mode_symbol;

  using rounding_modes = std::vector<ieee_floatt::rounding_modet>;
  static const rounding_modes all_rounding_modes;
};

const symbol_exprt constants_evaluator::rounding_mode_symbol =
  symbol_exprt(CPROVER_PREFIX "rounding_mode", signedbv_typet(32));

const constants_evaluator::rounding_modes
  constants_evaluator::all_rounding_modes{ieee_floatt::ROUND_TO_EVEN,
                                          ieee_floatt::ROUND_TO_ZERO,
                                          ieee_floatt::ROUND_TO_MINUS_INF,
                                          ieee_floatt::ROUND_TO_PLUS_INF};

abstract_object_pointert constants_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  auto evaluator = constants_evaluator(expr, environment, ns);
  return evaluator();
}

///////////////////////////////////////////////////////
// intervals expression transform
class interval_evaluator
{
public:
  interval_evaluator(
    const exprt &e,
    const std::vector<abstract_object_pointert> &ops,
    const abstract_environmentt &env,
    const namespacet &n)
    : expression(e), operands(ops), environment(env), ns(n)
  {
    PRECONDITION(expression.operands().size() == operands.size());
  }

  abstract_object_pointert operator()() const
  {
    return transform();
  }

private:
  using interval_abstract_value_pointert =
    sharing_ptrt<const interval_abstract_valuet>;

  abstract_object_pointert transform() const
  {
    auto interval_operands = operands_as_intervals();
    auto num_operands = interval_operands.size();

    if(num_operands != operands.size())
    {
      // We could not convert all operands into intervals,
      // e.g. if its type is not something we can represent as an interval,
      // try dispatching the expression_transform under that type instead.
      return constants_expression_transform(
        expression, operands, environment, ns);
    }

    if(num_operands == 0)
      return environment.abstract_object_factory(
        expression.type(), ns, true, false);

    if(expression.id() == ID_if)
      return interval_evaluate_conditional(interval_operands);

    if(num_operands == 1)
      return interval_evaluate_unary_expr(interval_operands);

    constant_interval_exprt result = interval_operands[0]->to_interval();

    for(size_t opIndex = 1; opIndex != interval_operands.size(); ++opIndex)
    {
      auto &interval_next = interval_operands[opIndex]->to_interval();
      result = result.eval(expression.id(), interval_next);
    }

    INVARIANT(
      result.type() == expression.type(),
      "Type of result interval should match expression type");
    return make_interval(expression.type(), result);
  }

  std::vector<interval_abstract_value_pointert> operands_as_intervals() const
  {
    std::vector<interval_abstract_value_pointert> interval_operands;

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
            return std::vector<interval_abstract_value_pointert>();

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
            iav =
              std::dynamic_pointer_cast<const interval_abstract_valuet>(ivop);
        }
        CHECK_RETURN(
          !std::dynamic_pointer_cast<const context_abstract_objectt>(iav));
      }

      if(iav)
        interval_operands.push_back(iav);
    }

    return interval_operands;
  }

  abstract_object_pointert interval_evaluate_conditional(
    const std::vector<interval_abstract_value_pointert> &interval_operands)
    const
  {
    auto const &condition_interval = interval_operands[0]->to_interval();
    auto const &true_interval = interval_operands[1]->to_interval();
    auto const &false_interval = interval_operands[2]->to_interval();

    auto condition_result = condition_interval.is_definitely_true();

    if(condition_result.is_unknown())
    {
      // Value of the condition is both true and false, so
      // combine the intervals of both the true and false expressions
      return make_interval(
        expression.type(),
        constant_interval_exprt(
          constant_interval_exprt::get_min(
            true_interval.get_lower(), false_interval.get_lower()),
          constant_interval_exprt::get_max(
            true_interval.get_upper(), false_interval.get_upper())));
    }

    return condition_result.is_true()
             ? make_interval(true_interval.type(), true_interval)
             : make_interval(false_interval.type(), false_interval);
  }

  abstract_object_pointert interval_evaluate_unary_expr(
    const std::vector<interval_abstract_value_pointert> &interval_operands)
    const
  {
    const constant_interval_exprt &operand_expr =
      interval_operands[0]->to_interval();

    if(expression.id() == ID_typecast)
    {
      const typecast_exprt &tce = to_typecast_expr(expression);

      const constant_interval_exprt &new_interval =
        operand_expr.typecast(tce.type());

      INVARIANT(
        new_interval.type() == expression.type(),
        "Type of result interval should match expression type");

      return make_interval(tce.type(), new_interval);
    }

    const constant_interval_exprt &interval_result =
      operand_expr.eval(expression.id());
    INVARIANT(
      interval_result.type() == expression.type(),
      "Type of result interval should match expression type");
    return make_interval(expression.type(), interval_result);
  }

  abstract_object_pointert
  make_interval(const typet &type, const exprt &expr) const
  {
    return environment.abstract_object_factory(type, expr, ns);
  }

  const exprt &expression;
  const std::vector<abstract_object_pointert> &operands;
  const abstract_environmentt &environment;
  const namespacet &ns;
};

abstract_object_pointert intervals_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  auto evaluator = interval_evaluator(expr, operands, environment, ns);
  return evaluator();
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
    return unwrapped_values.to_interval();

  const auto &type = new_values.first()->type();
  auto result = std::make_shared<value_set_abstract_objectt>(type);
  result->set_values(unwrapped_values);
  return result;
}
