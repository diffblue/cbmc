/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/monotonic_change.h>
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

// Ideally, the implementation of this function should be just
// return any_of_type<monotonic_changet>(operands);
// However, this causes an error when we run
// goto-cc toy.c -o toy.goto
// goto-analyzer --function main --vsd --vsd-values --monotonic-change
// --show toy.goto
// in the following C code:
// int main()
// {
//   int x = 0;
//   int y = (x + 1) * (x - 1);
// }
bool any_monotonic_changes(
  const std::vector<abstract_object_pointert> &operands)
{
  // return any_of_type<monotonic_changet>(operands);
  return std::find_if(
           operands.begin(),
           operands.end(),
           [](const abstract_object_pointert &p) {
             return (
               std::dynamic_pointer_cast<const monotonic_changet>(p) !=
               nullptr);
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
  if(any_monotonic_changes(operands))
    return monotonic_change_expression_transform(nullptr, nil_exprt(), expr);
  return constants_expression_transform(expr, operands, environment, ns);
}

static abstract_object_pointert assign_transform(
  const abstract_object_pointert &lhs_abstract_object,
  const exprt &lhs,
  const exprt &rhs,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(any_value_sets(operands))
    return value_set_expression_transform(rhs, operands, environment, ns);
  if(any_intervals(operands))
    return intervals_expression_transform(rhs, operands, environment, ns);
  if(any_monotonic_changes(operands))
    return monotonic_change_expression_transform(lhs_abstract_object, lhs, rhs);
  return constants_expression_transform(rhs, operands, environment, ns);
}

abstract_object_pointert abstract_value_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return transform(expr, operands, environment, ns);
}

abstract_object_pointert abstract_value_objectt::assign_expression_transform(
  const abstract_object_pointert &lhs_abstract_object,
  const exprt &lhs,
  const exprt &rhs,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return assign_transform(
    lhs_abstract_object, lhs, rhs, operands, environment, ns);
}

abstract_object_pointert abstract_value_objectt::read(
  const abstract_environmentt &environment,
  const exprt &specifier,
  const namespacet &ns) const
{
  UNREACHABLE; // Should not ever call read on a value;
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
    const std::vector<abstract_object_pointert> &ops,
    const abstract_environmentt &env,
    const namespacet &n)
    : expression(e), operands(ops), environment(env), ns(n)
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
    auto expr = adjust_expression_for_rounding_mode();

    auto operand_is_top = false;
    for(size_t i = 0; i != operands.size(); ++i)
    {
      auto lhs_value = operands[i]->to_constant();

      // do not give up if a sub-expression is not a constant,
      // because the whole expression may still be simplified in some cases
      // (eg multiplication by zero)
      if(lhs_value.is_not_nil())
        expr.operands()[i] = lhs_value;
      else
        operand_is_top = true;
    }

    auto simplified = simplify_expr(expr, ns);

    if(simplified.has_operands() && operand_is_top)
      return top(simplified.type());

    // the expression is fully simplified
    return std::make_shared<constant_abstract_valuet>(
      simplified, environment, ns);
  }

  abstract_object_pointert try_transform_expr_with_all_rounding_modes() const
  {
    abstract_object_pointert last_result;

    auto results_differ = [](
                            const abstract_object_pointert &prev,
                            const abstract_object_pointert &cur) {
      if(prev == nullptr)
        return false;
      return prev->to_constant() != cur->to_constant();
    };

    for(auto rounding_mode : all_rounding_modes)
    {
      auto child_env(environment_with_rounding_mode(rounding_mode));
      auto child_operands =
        reeval_operands(expression.operands(), child_env, ns);

      auto result =
        constants_evaluator(expression, child_operands, child_env, ns)();

      if(result->is_top() || results_differ(last_result, result))
        return top(expression.type());
      last_result = result;
    }

    return last_result;
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

    if(adjusted_expr != expression)
      operands = reeval_operands(adjusted_expr.operands(), environment, ns);

    return adjusted_expr;
  }

  static std::vector<abstract_object_pointert> reeval_operands(
    const exprt::operandst &ops,
    const abstract_environmentt &env,
    const namespacet &ns)
  {
    auto reevaled_operands = std::vector<abstract_object_pointert>{};
    std::transform(
      ops.cbegin(),
      ops.end(),
      std::back_inserter(reevaled_operands),
      [&env, &ns](const exprt &op) { return env.eval(op, ns); });
    return reevaled_operands;
  }

  abstract_object_pointert top(const typet &type) const
  {
    return make_top<constant_abstract_valuet>(type);
  }

  bool rounding_mode_is_not_set() const
  {
    auto rounding_mode =
      environment.eval(rounding_mode_symbol, ns)->to_constant();
    return rounding_mode.is_nil();
  }

  const exprt &expression;
  mutable std::vector<abstract_object_pointert> operands;
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
  auto evaluator = constants_evaluator(expr, operands, environment, ns);
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

///////////////////////////////////////////////////////
// Monotonic change expression transform
class monotonic_change_evaluatort
{
public:
  monotonic_change_evaluatort(
    const abstract_object_pointert &l_object,
    const exprt &l_expr,
    const exprt &r_expr)
    : lhs_abstract_object(l_object), lhs(l_expr), rhs(r_expr)
  {
    // PRECONDITION(rhs.operands().size() == operands.size());
  }

  abstract_object_pointert operator()() const
  {
    return transform(rhs);
  }

private:
  using interval_abstract_value_pointert =
    sharing_ptrt<const interval_abstract_valuet>;

  abstract_object_pointert transform(const exprt &expr) const
  {
    // If we do not know the abstract object of the left-hand side of an
    // assignment, we simply return the "top."
    if(lhs_abstract_object == nullptr)
      return make_top<monotonic_changet>(expr.type());

    std::shared_ptr<const monotonic_changet> lhs_abstract_object_unwrapped =
      std::dynamic_pointer_cast<const monotonic_changet>(
        lhs_abstract_object->unwrap_context());

    // If the left-hand side of an assignment is not a monotonic-change object,
    // we simply return the "top." Can such a situation arise?
    if(lhs_abstract_object_unwrapped == nullptr)
      return make_top<monotonic_changet>(expr.type());

    monotonicity_flags mvalue =
      lhs_abstract_object_unwrapped->monotonicity_value;

    // This case handles an assignment whose right-hand side is a ternary
    // expression; e.g. x := bool_expr ? (x + 1) : (x - 1).
    if(expr.id() == ID_if)
    {
      return evaluate_conditional();
    }

    // This case handles an assignment of the form x := x + n or x
    // := x - n, where x is an lvalue and n is a constant number. When C is
    // compiled to GOTO, x++ is translated to x := x + 1. Likewise, x-- is
    // translated to x := x - 1. Hence, we do not need to be concerned with x++
    // and x-- - we can focus on assignments of the form x := x + n and x := x -
    // n.
    // Is it correct to use == to test the equality of two expressions?
    if(
      (expr.id() == ID_plus || expr.id() == ID_minus) &&
      expr.operands()[1].id() == ID_constant && expr.operands()[0] == lhs)
    {
      mp_integer constant_value =
        numeric_cast_v<mp_integer>(to_constant_expr(expr.operands()[1]));

      switch(mvalue)
      {
      case top_or_bottom:
        if(lhs_abstract_object_unwrapped->is_bottom())
          return std::make_shared<monotonic_changet>(expr.type(), false, true);
        else
          return make_top<monotonic_changet>(expr.type());
        break;
      case strict_increase:
        if(
          (expr.id() == ID_plus && constant_value >= 0) ||
          (expr.id() == ID_minus && constant_value <= 0))
          return std::make_shared<monotonic_changet>(
            expr.type(), false, false, strict_increase);
        else
          return make_top<monotonic_changet>(expr.type());
        break;
      case unchanged:
        if(
          (expr.id() == ID_plus && constant_value > 0) ||
          (expr.id() == ID_minus && constant_value < 0))
          return std::make_shared<monotonic_changet>(
            expr.type(), false, false, strict_increase);
        else if(constant_value == 0)
          return std::make_shared<monotonic_changet>(
            expr.type(), false, false, unchanged);
        else
          return std::make_shared<monotonic_changet>(
            expr.type(), false, false, strict_decrease);
        break;
      case strict_decrease:
        if(
          (expr.id() == ID_plus && constant_value <= 0) ||
          (expr.id() == ID_minus && constant_value >= 0))
          return std::make_shared<monotonic_changet>(
            expr.type(), false, false, strict_decrease);
        else
          return make_top<monotonic_changet>(expr.type());
        break;
      }
    }

    return make_top<monotonic_changet>(expr.type());
  }

  abstract_object_pointert evaluate_conditional() const
  {
    const exprt &true_branch_expr = rhs.operands()[1];
    const exprt &false_branch_expr = rhs.operands()[2];
    abstract_object_pointert true_abstract_object = transform(true_branch_expr);
    abstract_object_pointert false_abstract_object =
      transform(false_branch_expr);

    return abstract_objectt::merge(
             true_abstract_object, false_abstract_object, widen_modet::no)
      .object;
  }

  const abstract_object_pointert &lhs_abstract_object;
  const exprt &lhs;
  const exprt &rhs;
};

abstract_object_pointert monotonic_change_expression_transform(
  const abstract_object_pointert &lhs_abstract_object,
  const exprt &lhs,
  const exprt &rhs)
{
  auto evaluator = monotonic_change_evaluatort(lhs_abstract_object, lhs, rhs);
  return evaluator();
}

abstract_value_pointert
abstract_value_objectt::as_value(const abstract_object_pointert &obj) const
{
  return std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
}
