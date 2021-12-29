/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/optional.h>
#include <util/range.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>

/// A method to detect equivalence between experts that can contain typecast
static bool expr_eq(const exprt &expr1, const exprt &expr2)
{
  return skip_typecast(expr1) == skip_typecast(expr2);
}

/// To obtain the min value for the quantifier variable of the specified
/// forall/exists operator. The min variable is in the form of "!(var_expr >
/// constant)".
static optionalt<constant_exprt>
get_quantifier_var_min(const exprt &var_expr, const exprt &quantifier_expr)
{
  if(quantifier_expr.id()==ID_or)
  {
    /**
     * The min variable
     * is in the form of "!(var_expr >= constant)".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_not)
        continue;
      exprt y = to_not_expr(x).op();
      if(y.id()!=ID_ge)
        continue;
      const auto &y_binary = to_binary_relation_expr(y);
      if(
        expr_eq(var_expr, y_binary.lhs()) && y_binary.rhs().id() == ID_constant)
      {
        return to_constant_expr(y_binary.rhs());
      }
    }

    if(var_expr.type().id() == ID_unsignedbv)
      return from_integer(0, var_expr.type());
  }
  else if(quantifier_expr.id() == ID_and)
  {
    /**
     * The min variable
     * is in the form of "var_expr >= constant".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_ge)
        continue;
      const auto &x_binary = to_binary_relation_expr(x);
      if(
        expr_eq(var_expr, x_binary.lhs()) && x_binary.rhs().id() == ID_constant)
      {
        return to_constant_expr(x_binary.rhs());
      }
    }

    if(var_expr.type().id() == ID_unsignedbv)
      return from_integer(0, var_expr.type());
  }

  return {};
}

/// To obtain the max value for the quantifier variable of the specified
/// forall/exists operator.
static optionalt<constant_exprt>
get_quantifier_var_max(const exprt &var_expr, const exprt &quantifier_expr)
{
  if(quantifier_expr.id()==ID_or)
  {
    /**
     * The max variable
     * is in the form of "var_expr >= constant".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_ge)
        continue;
      const auto &x_binary = to_binary_relation_expr(x);
      if(
        expr_eq(var_expr, x_binary.lhs()) && x_binary.rhs().id() == ID_constant)
      {
        const constant_exprt &over_expr = to_constant_expr(x_binary.rhs());

        mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);

        /**
         * Due to the ''simplify'',
         * the ''over_i'' value we obtain here is not the exact
         * maximum index as specified in the original code.
         **/
        over_i-=1;
        return from_integer(over_i, x_binary.rhs().type());
      }
    }
  }
  else
  {
    /**
     * The max variable
     * is in the form of "!(var_expr >= constant)".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_not)
        continue;
      exprt y = to_not_expr(x).op();
      if(y.id()!=ID_ge)
        continue;
      const auto &y_binary = to_binary_relation_expr(y);
      if(
        expr_eq(var_expr, y_binary.lhs()) && y_binary.rhs().id() == ID_constant)
      {
        const constant_exprt &over_expr = to_constant_expr(y_binary.rhs());
        mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);
        over_i-=1;
        return from_integer(over_i, y_binary.rhs().type());
      }
    }
  }

  return {};
}

static optionalt<exprt> eager_quantifier_instantiation(
  const quantifier_exprt &expr,
  const namespacet &ns)
{
  const symbol_exprt &var_expr = expr.symbol();

  /**
   * We need to rewrite the forall/exists quantifier into
   * an OR/AND expr.
   **/

  const exprt re = simplify_expr(expr.where(), ns);

  if(re.is_true() || re.is_false())
  {
    return re;
  }

  const optionalt<constant_exprt> min_i = get_quantifier_var_min(var_expr, re);
  const optionalt<constant_exprt> max_i = get_quantifier_var_max(var_expr, re);

  if(!min_i.has_value() || !max_i.has_value())
    return nullopt;

  mp_integer lb = numeric_cast_v<mp_integer>(min_i.value());
  mp_integer ub = numeric_cast_v<mp_integer>(max_i.value());

  if(lb>ub)
    return nullopt;

  std::vector<exprt> expr_insts;
  for(mp_integer i=lb; i<=ub; ++i)
  {
    exprt constraint_expr = re;
    replace_expr(var_expr,
                 from_integer(i, var_expr.type()),
                 constraint_expr);
    expr_insts.push_back(constraint_expr);
  }

  if(expr.id()==ID_forall)
  {
    // maintain the domain constraint if it isn't guaranteed by the
    // instantiations (for a disjunction the domain constraint is implied by the
    // instantiations)
    if(re.id() == ID_and)
    {
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_gt, from_integer(lb, var_expr.type())));
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_le, from_integer(ub, var_expr.type())));
    }
    return simplify_expr(conjunction(expr_insts), ns);
  }
  else if(expr.id() == ID_exists)
  {
    // maintain the domain constraint if it isn't trivially satisfied by the
    // instantiations (for a conjunction the instantiations are stronger
    // constraints)
    if(re.id() == ID_or)
    {
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_gt, from_integer(lb, var_expr.type())));
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_le, from_integer(ub, var_expr.type())));
    }
    return simplify_expr(disjunction(expr_insts), ns);
  }

  UNREACHABLE;
}

literalt boolbvt::convert_quantifier(const quantifier_exprt &src)
{
  PRECONDITION(src.id() == ID_forall || src.id() == ID_exists);

  // We first worry about the scoping of the symbols bound by the quantifier.
  auto fresh_symbols = fresh_binding(src);

  // replace in where()
  auto where_replaced = src.instantiate(fresh_symbols);

  // produce new quantifier expression
  auto new_src =
    quantifier_exprt(src.id(), std::move(fresh_symbols), where_replaced);

  const auto res = eager_quantifier_instantiation(src, ns);

  if(res)
    return convert_bool(*res);

  // we failed to instantiate here, need to pass to post-processing
  quantifier_list.emplace_back(quantifiert(src, prop.new_variable()));

  return quantifier_list.back().l;
}

void boolbvt::post_process_quantifiers()
{
  if(quantifier_list.empty())
    return;

  // we do not yet have any elaborate post-processing
  for(const auto &q : quantifier_list)
    conversion_failed(q.expr);
}
