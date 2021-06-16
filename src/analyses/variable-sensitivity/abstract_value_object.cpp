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
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/make_unique.h>
#include <util/simplify_expr.h>

#include <algorithm>

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

template <class representation_type>
bool any_of_type(const std::vector<abstract_object_pointert> &operands)
{
  return std::find_if(
           operands.begin(),
           operands.end(),
           [](const abstract_object_pointert &p) {
             return (!p->is_top()) &&
                    (std::dynamic_pointer_cast<const representation_type>(p) !=
                     nullptr);
           }) != operands.end();
}

bool any_value_sets(const std::vector<abstract_object_pointert> &operands)
{
  return any_of_type<value_set_abstract_objectt>(operands);
}

bool any_intervals(const std::vector<abstract_object_pointert> &operands)
{
  return any_of_type<interval_abstract_valuet>(operands);
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

abstract_object_pointert abstract_value_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  UNREACHABLE; // Should not ever call write on a value;
}

abstract_object_pointert abstract_value_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const abstract_value_objectt>(other);
  if(cast_other)
    return merge_with_value(cast_other, widen_mode);

  return abstract_objectt::merge(other, widen_mode);
}

abstract_object_pointert
abstract_value_objectt::meet(const abstract_object_pointert &other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const abstract_value_objectt>(other);
  if(cast_other)
    return meet_with_value(cast_other);

  return abstract_objectt::meet(other);
}

// evaluation helpers
template <class representation_type>
abstract_object_pointert make_top(const typet &type)
{
  return std::make_shared<representation_type>(type, true, false);
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
    return std::make_shared<constant_abstract_valuet>(
      simplified, environment, ns);
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
    return make_top<constant_abstract_valuet>(type);
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
      return make_top<interval_abstract_valuet>(expression.type());

    if(expression.id() == ID_if)
      return evaluate_conditional(interval_operands);

    if(num_operands == 1)
      return evaluate_unary_expr(interval_operands);

    constant_interval_exprt result = interval_operands[0];

    for(size_t opIndex = 1; opIndex != interval_operands.size(); ++opIndex)
    {
      auto &interval_next = interval_operands[opIndex];
      result = result.eval(expression.id(), interval_next);
    }

    INVARIANT(
      result.type() == expression.type(),
      "Type of result interval should match expression type");
    return make_interval(result);
  }

  std::vector<constant_interval_exprt> operands_as_intervals() const
  {
    std::vector<constant_interval_exprt> interval_operands;

    for(const auto &op : operands)
    {
      auto iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(op);
      if(!iav)
      {
        // The operand isn't an interval
        // if it's an integral constant we can convert it into an interval.
        if(constant_interval_exprt::is_int(op->type()))
        {
          const auto op_as_constant = op->to_constant();
          if(op_as_constant.is_nil())
            return std::vector<constant_interval_exprt>();

          iav = make_interval(op_as_constant);
        }
        CHECK_RETURN(
          !std::dynamic_pointer_cast<const context_abstract_objectt>(iav));
      }

      if(iav)
        interval_operands.push_back(iav->to_interval());
    }

    return interval_operands;
  }

  abstract_object_pointert evaluate_conditional(
    const std::vector<constant_interval_exprt> &interval_operands) const
  {
    auto const &condition_interval = interval_operands[0];
    auto const &true_interval = interval_operands[1];
    auto const &false_interval = interval_operands[2];

    auto condition_result = condition_interval.is_definitely_true();

    if(condition_result.is_unknown())
    {
      // Value of the condition is both true and false, so
      // combine the intervals of both the true and false expressions
      return make_interval(constant_interval_exprt(
        constant_interval_exprt::get_min(
          true_interval.get_lower(), false_interval.get_lower()),
        constant_interval_exprt::get_max(
          true_interval.get_upper(), false_interval.get_upper())));
    }

    return condition_result.is_true() ? make_interval(true_interval)
                                      : make_interval(false_interval);
  }

  abstract_object_pointert evaluate_unary_expr(
    const std::vector<constant_interval_exprt> &interval_operands) const
  {
    const constant_interval_exprt &operand_expr = interval_operands[0];

    if(expression.id() == ID_typecast)
    {
      const typecast_exprt &tce = to_typecast_expr(expression);

      const constant_interval_exprt &new_interval =
        operand_expr.typecast(tce.type());

      INVARIANT(
        new_interval.type() == expression.type(),
        "Type of result interval should match expression type");

      return make_interval(new_interval);
    }

    const constant_interval_exprt &interval_result =
      operand_expr.eval(expression.id());
    INVARIANT(
      interval_result.type() == expression.type(),
      "Type of result interval should match expression type");
    return make_interval(interval_result);
  }

  interval_abstract_value_pointert make_interval(const exprt &expr) const
  {
    return interval_abstract_valuet::make_interval(expr, environment, ns);
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
class value_set_evaluator
{
public:
  value_set_evaluator(
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
  abstract_object_pointert transform() const
  {
    auto ranges = operands_as_ranges();

    if(expression.id() == ID_if)
      return evaluate_conditional(ranges);

    auto resulting_objects = evaluate_each_combination(ranges);

    return value_set_abstract_objectt::make_value_set(resulting_objects);
  }

  /// Evaluate expression for every combination of values in \p value_ranges.
  /// <{1,2},{1},{1,2,3}> ->
  ///   eval(1,1,1), eval(1,1,2), eval(1,1,3), eval(2,1,1), eval(2,1,2), eval(2,1,3).
  abstract_object_sett
  evaluate_each_combination(const std::vector<value_ranget> &value_ranges) const
  {
    abstract_object_sett results;
    std::vector<abstract_object_pointert> combination;
    evaluate_combination(results, value_ranges, combination);
    return results;
  }

  void evaluate_combination(
    abstract_object_sett &results,
    const std::vector<value_ranget> &value_ranges,
    std::vector<abstract_object_pointert> &combination) const
  {
    size_t n = combination.size();
    if(n == value_ranges.size())
    {
      auto rewritten_expr = rewrite_expression(combination);
      auto result = ::transform(rewritten_expr, combination, environment, ns);
      results.insert(result);
    }
    else
    {
      for(const auto &value : value_ranges[n])
      {
        combination.push_back(value);
        evaluate_combination(results, value_ranges, combination);
        combination.pop_back();
      }
    }
  }

  exprt
  rewrite_expression(const std::vector<abstract_object_pointert> &ops) const
  {
    auto operands_expr = exprt::operandst{};
    for(size_t i = 0; i != expression.operands().size(); ++i)
    {
      const auto &v = ops[i];
      if(is_constant_value(v))
        operands_expr.push_back(v->to_constant());
      else
        operands_expr.push_back(expression.operands()[i]);
    }
    auto rewritten_expr =
      exprt(expression.id(), expression.type(), std::move(operands_expr));
    return rewritten_expr;
  }

  static bool is_constant_value(const abstract_object_pointert &v)
  {
    return std::dynamic_pointer_cast<const constant_abstract_valuet>(v) !=
           nullptr;
  }

  std::vector<value_ranget> operands_as_ranges() const
  {
    auto unwrapped = std::vector<value_ranget>{};

    for(const auto &op : operands)
    {
      auto av = std::dynamic_pointer_cast<const abstract_value_objectt>(
        op->unwrap_context());
      INVARIANT(av, "should be an abstract value object");
      unwrapped.emplace_back(av->value_range());
    }

    return unwrapped;
  }

  static abstract_object_pointert
  evaluate_conditional(const std::vector<value_ranget> &ops)
  {
    auto const &condition = ops[0];

    auto const &true_result = ops[1];
    auto const &false_result = ops[2];

    auto all_true = true;
    auto all_false = true;
    for(const auto &v : condition)
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
    return value_set_abstract_objectt::make_value_set(resulting_objects);
  }

  const exprt &expression;
  const std::vector<abstract_object_pointert> &operands;
  const abstract_environmentt &environment;
  const namespacet &ns;
};

static abstract_object_pointert value_set_expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  auto evaluator = value_set_evaluator(expr, operands, environment, ns);
  return evaluator();
}

abstract_value_pointert
abstract_value_objectt::as_value(const abstract_object_pointert &obj) const
{
  return std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
}
