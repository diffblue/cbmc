/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>

#include "boolbv.h"

/*******************************************************************\

Function: expr_eq

  Inputs:

 Outputs:

 Purpose: A method to detect equivalence between experts that can
          contain typecast

\*******************************************************************/

bool expr_eq(const exprt &expr1, const exprt &expr2)
{
  exprt e1=expr1, e2=expr2;
  if(expr1.id()==ID_typecast) e1=expr1.op0();
  if(expr2.id()==ID_typecast) e2=expr2.op0();
  return e1==e2;
}

/*******************************************************************\

Function: get_quantifier_var_min

  Inputs:

 Outputs:

 Purpose: To obtain the min value for the quantifier variable
          of the specified forall/exists operator. The min variable
          is in the form of "!(var_expr > constant)".

\*******************************************************************/

exprt get_quantifier_var_min(
  const exprt &var_expr,
  const exprt &quantifier_expr)
{
  assert(quantifier_expr.id()==ID_or ||
         quantifier_expr.id()==ID_and);
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
      if(x.id()!=ID_not) continue;
      exprt y=x.op0();
      if(y.id()!=ID_ge) continue;
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
      if(x.id()!=ID_ge) continue;
      if(expr_eq(var_expr, x.op0()) && x.op1().id()==ID_constant)
      {
        return x.op1();
      }
    }
  }
  return res;
}

/*******************************************************************\

Function: get_quantifier_var_max

  Inputs:

 Outputs:

 Purpose: To obtain the max value for the quantifier variable
          of the specified forall/exists operator.

\*******************************************************************/

exprt get_quantifier_var_max(
  const exprt &var_expr,
  const exprt &quantifier_expr)
{
  assert(quantifier_expr.id()==ID_or ||
         quantifier_expr.id()==ID_and);
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
      if(x.id()!=ID_ge) continue;
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
      if(x.id()!=ID_not) continue;
      exprt y=x.op0();
      if(y.id()!=ID_ge) continue;
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

/*******************************************************************\

Function: instantiate_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool instantiate_quantifier(exprt &expr,
                            const namespacet &ns)
{
  if(!(expr.id()==ID_forall || expr.id()==ID_exists))
    return true;

  assert(expr.operands().size()==2);
  assert(expr.op0().id()==ID_symbol);

  exprt var_expr=expr.op0();

  /**
   * We need to rewrite the forall/exists quantifier into
   * an OR/AND expr.
   **/
  exprt re(expr);
  exprt tmp(re.op1());
  re.swap(tmp);
  re=simplify_expr(re, ns);

  if(re.is_true() || re.is_false())
  {
    expr=re;
    return true;
  }

  exprt min_i=get_quantifier_var_min(var_expr, re);
  exprt max_i=get_quantifier_var_max(var_expr, re);
  exprt body_expr=re;
  if(var_expr.is_false() ||
     min_i.is_false() ||
     max_i.is_false() ||
     body_expr.is_false())
    return false;

  mp_integer lb, ub;
  to_integer(min_i, lb);
  to_integer(max_i, ub);

  if(lb>ub)
    return false;

  bool res=true;
  std::vector<exprt> expr_insts;
  for(mp_integer i=lb; i<=ub; ++i)
  {
    exprt constraint_expr=body_expr;
    replace_expr(var_expr,
                 from_integer(i, var_expr.type()),
                 constraint_expr);
    expr_insts.push_back(constraint_expr);
  }
  if(expr.id()==ID_forall)
  {
    expr=conjunction(expr_insts);
  }
  if(expr.id()==ID_exists)
  {
    expr=disjunction(expr_insts);
  }

  return res;
}

/*******************************************************************\

Function: boolbvt::convert_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_quantifier(const exprt &src)
{
  exprt expr(src);
  if(!instantiate_quantifier(expr, ns))
    return SUB::convert_rest(src);

  quantifiert quantifier;
  quantifier.expr=expr;
  quantifier_list.push_back(quantifier);

  literalt l=prop.new_variable();
  quantifier_list.back().l=l;

  return l;
}

/*******************************************************************\

Function: boolbvt::post_process_quantifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::post_process_quantifiers()
{
  std::set<exprt> instances;

  if(quantifier_list.empty()) return;

  for(auto it=quantifier_list.begin();
      it!=quantifier_list.end();
      ++it)
  {
    prop.set_equal(convert_bool(it->expr), it->l);
  }
}
