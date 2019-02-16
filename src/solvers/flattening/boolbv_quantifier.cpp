/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/optional.h>
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
static exprt
get_quantifier_var_min(const exprt &var_expr, const exprt &quantifier_expr)
{
  PRECONDITION(quantifier_expr.id() == ID_or || quantifier_expr.id() == ID_and);

  exprt res = false_exprt();
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
      exprt y=x.op0();
      if(y.id()!=ID_ge)
        continue;
      if(expr_eq(var_expr, y.op0()) && y.op1().id()==ID_constant)
      {
        return y.op1();
      }
    }
  }
  else
  {
    /**
     * The min variable
     * is in the form of "var_expr >= constant".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_ge)
        continue;
      if(expr_eq(var_expr, x.op0()) && x.op1().id()==ID_constant)
      {
        return x.op1();
      }
    }
  }
  return res;
}

/// To obtain the max value for the quantifier variable of the specified
/// forall/exists operator.
static exprt
get_quantifier_var_max(const exprt &var_expr, const exprt &quantifier_expr)
{
  PRECONDITION(quantifier_expr.id() == ID_or || quantifier_expr.id() == ID_and);
  exprt res = false_exprt();
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
      if(expr_eq(var_expr, x.op0()) && x.op1().id()==ID_constant)
      {
        const constant_exprt &over_expr = to_constant_expr(x.op1());

        mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);

        /**
         * Due to the ''simplify'',
         * the ''over_i'' value we obtain here is not the exact
         * maximum index as specified in the original code.
         **/
        over_i-=1;
        res=from_integer(over_i, x.op1().type());
        return res;
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
      exprt y=x.op0();
      if(y.id()!=ID_ge)
        continue;
      if(expr_eq(var_expr, y.op0()) && y.op1().id()==ID_constant)
      {
        const constant_exprt &over_expr = to_constant_expr(y.op1());
        mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);
        over_i-=1;
        res=from_integer(over_i, y.op1().type());
        return res;
      }
    }
  }
  return res;
}

static optionalt<exprt>
instantiate_quantifier(const quantifier_exprt &expr, const namespacet &ns)
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

  const exprt min_i = get_quantifier_var_min(var_expr, re);
  const exprt max_i = get_quantifier_var_max(var_expr, re);

  if(min_i.is_false() || max_i.is_false())
    return nullopt;

  mp_integer lb = numeric_cast_v<mp_integer>(to_constant_expr(min_i));
  mp_integer ub = numeric_cast_v<mp_integer>(to_constant_expr(max_i));

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

  const auto res = instantiate_quantifier(src, ns);

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
