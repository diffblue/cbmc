/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <array>
#include <goto-programs/adjust_float_expressions.h>
#include <langapi/language_util.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/type.h>

#include "abstract_environment.h"
#include "constant_abstract_value.h"

class constant_index_ranget : public single_value_index_ranget
{
public:
  explicit constant_index_ranget(const exprt &val)
    : single_value_index_ranget(val)
  {
  }
};

index_range_ptrt make_constant_index_range(const exprt &val)
{
  return std::make_shared<constant_index_ranget>(val);
}

constant_abstract_valuet::constant_abstract_valuet(const typet &t)
  : abstract_value_objectt(t), value()
{
}

constant_abstract_valuet::constant_abstract_valuet(
  const typet &t,
  bool tp,
  bool bttm)
  : abstract_value_objectt(t, tp, bttm), value()
{
}

constant_abstract_valuet::constant_abstract_valuet(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(e.type(), false, false), value(e)
{
}

index_range_ptrt
constant_abstract_valuet::index_range(const namespacet &ns) const
{
  exprt val = to_constant();
  if(!val.is_constant())
    return make_indeterminate_index_range();

  return make_constant_index_range(val);
}

abstract_object_pointert constant_abstract_valuet::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
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

abstract_object_pointert
constant_abstract_valuet::try_transform_expr_with_all_rounding_modes(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns) const
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
      expression_transform(expr, dummy, child_env, ns));
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

exprt constant_abstract_valuet::to_constant() const
{
  if(!is_top() && !is_bottom())
  {
    return this->value;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
}

void constant_abstract_valuet::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    out << from_expr(to_constant_expr(value));
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

abstract_object_pointert
constant_abstract_valuet::merge(abstract_object_pointert other) const
{
  constant_abstract_value_pointert cast_other =
    std::dynamic_pointer_cast<const constant_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_constant_constant(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return abstract_objectt::merge(other);
  }
}

abstract_object_pointert constant_abstract_valuet::merge_constant_constant(
  const constant_abstract_value_pointert &other) const
{
  if(is_bottom())
  {
    return std::make_shared<constant_abstract_valuet>(*other);
  }
  else
  {
    // Can we actually merge these value
    if(value == other->value)
    {
      return shared_from_this();
    }
    else
    {
      return abstract_objectt::merge(other);
    }
  }
}

void constant_abstract_valuet::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_constants;
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
