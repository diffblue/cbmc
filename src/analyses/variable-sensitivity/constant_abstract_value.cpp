/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <array>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/simplify_expr.h>
#include <util/type.h>
#include <goto-programs/adjust_float_expressions.h>
#include <util/ieee_float.h>
#include <util/arith_tools.h>


#include "abstract_enviroment.h"
#include "constant_abstract_value.h"

constant_abstract_valuet::constant_abstract_valuet(typet t):
  abstract_valuet(t), value()
{}

constant_abstract_valuet::constant_abstract_valuet(typet t, bool tp, bool bttm):
  abstract_valuet(t, tp, bttm), value()
{}

constant_abstract_valuet::constant_abstract_valuet(
  const exprt e,
  const abstract_environmentt &environment,
  const namespacet &ns):
    abstract_valuet(e.type(), false, false), value(e)
{}

abstract_object_pointert constant_abstract_valuet::expression_transform(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  // try finding the rounding mode. If it's not constant, try
  // seeing if we can get the same result with all rounding modes
  auto rounding_mode_symbol =
    symbol_exprt("__CPROVER_rounding_mode", signedbv_typet(32));
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
    abstract_object_pointert lhs_abstract_object=environment.eval(op, ns);
    const exprt &lhs_value=lhs_abstract_object->to_constant();
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
    symbol_exprt("__CPROVER_rounding_mode", signedbv_typet(32));
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
    possible_results.push_back(expression_transform(expr, child_env, ns));
  }
  auto first = possible_results.front()->to_constant();
  for(auto const &possible_result : possible_results)
  {
    auto current = possible_result->to_constant();
    if(current.is_nil() || current != first)
    {
      return environment.abstract_object_factory(expr.type(), ns);
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
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    out << to_constant_expr(value).get_value();
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

/*******************************************************************\

Function: constant_abstract_valuet::merge

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns the result of the merge

 Purpose: Attempts to do a constant/constant merge if both are constants,
          otherwise falls back to the parent merge


\*******************************************************************/

abstract_object_pointert constant_abstract_valuet::merge(
  abstract_object_pointert other) const
{
  constant_abstract_value_pointert cast_other=
    std::dynamic_pointer_cast<const constant_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_constant_constant(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return abstract_valuet::merge(other);
  }
}

/*******************************************************************\

Function: constant_abstract_valuet::merge_constant_constant

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns a new abstract object that is the result of the merge
          unless the merge is the same as this abstract object, in which
          case it returns this.

 Purpose: Merges another constant abstract value into this one

\*******************************************************************/

abstract_object_pointert constant_abstract_valuet::merge_constant_constant(
  constant_abstract_value_pointert other) const
{
  if(is_bottom())
  {
    return std::make_shared<constant_abstract_valuet>(*other);
  }
  else
  {
    // Can we actually merge these value
    if(value==other->value)
    {
      return shared_from_this();
    }
    else
    {
      return abstract_valuet::merge(other);
    }
  }
}
