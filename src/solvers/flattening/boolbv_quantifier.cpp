/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/optional.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>

/// A method to detect equivalence between experts that can contain typecast
bool expr_eq(const exprt &expr1, const exprt &expr2)
{
  exprt e1=expr1, e2=expr2;
  if(expr1.id()==ID_typecast)
    e1=expr1.op0();
  if(expr2.id()==ID_typecast)
    e2=expr2.op0();
  return e1==e2;
}

/// To obtain the min value for the quantifier variable of the specified
/// forall/exists operator. The min variable is in the form of "!(var_expr >
/// constant)".
exprt get_quantifier_var_min(
  const exprt &var_expr,
  const exprt &quantifier_expr)
{
  PRECONDITION(quantifier_expr.id() == ID_or || quantifier_expr.id() == ID_and);

  exprt res;
  res.make_false();
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
exprt get_quantifier_var_max(
  const exprt &var_expr,
  const exprt &quantifier_expr)
{
  PRECONDITION(quantifier_expr.id() == ID_or || quantifier_expr.id() == ID_and);
  exprt res;
  res.make_false();
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
        exprt over_expr=x.op1();
        mp_integer over_i;
        to_integer(over_expr, over_i);
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
        exprt over_expr=y.op1();
        mp_integer over_i;
        to_integer(over_expr, over_i);
        over_i-=1;
        res=from_integer(over_i, y.op1().type());
        return res;
      }
    }
  }
  return res;
}

optionalt<exprt>
instantiate_quantifier(const quantifier_exprt &expr, const namespacet &ns)
{
  PRECONDITION(expr.id() == ID_forall || expr.id() == ID_exists);

  const symbol_exprt &var_expr = expr.symbol();

  /**
   * We need to rewrite the forall/exists quantifier into
   * an OR/AND expr.
   **/

  const exprt &re = simplify_expr(expr.where(), ns);

  if(re.is_true() || re.is_false())
  {
    return re;
  }

  const exprt &min_i = get_quantifier_var_min(var_expr, re);
  const exprt &max_i = get_quantifier_var_max(var_expr, re);

  if(min_i.is_false() || max_i.is_false())
    return nullopt;

  mp_integer lb = numeric_cast_v<mp_integer>(min_i);
  mp_integer ub = numeric_cast_v<mp_integer>(max_i);

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
    return conjunction(expr_insts);
  }
  else if(expr.id() == ID_exists)
  {
    return disjunction(expr_insts);
  }

  UNREACHABLE;
  return nullopt;
}

literalt boolbvt::convert_quantifier(const quantifier_exprt &src)
{
  PRECONDITION(src.id() == ID_forall || src.id() == ID_exists);

  quantifier_exprt expr(src);
  const auto res = instantiate_quantifier(expr, ns);

  if(!res)
  {
    return SUB::convert_rest(src);
  }

  quantifiert quantifier;
  quantifier.expr = *res;
  quantifier_list.push_back(quantifier);

  literalt l=prop.new_variable();
  quantifier_list.back().l=l;

  return l;
}

void boolbvt::post_process_quantifiers()
{
  std::set<exprt> instances;

  if(quantifier_list.empty())
    return;

  for(auto it=quantifier_list.begin();
      it!=quantifier_list.end();
      ++it)
  {
    prop.set_equal(convert_bool(it->expr), it->l);
  }
}
