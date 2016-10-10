/*******************************************************************\

Module: The implementation in this file aims to simplify a quantifier 
        expression. Note that if a quantifier forall/exists
        is used at the scope of an assertion, it is not handled here.

Author: 

\*******************************************************************/

#include "simplify_expr_class.h"
#include "std_expr.h"
#include "arith_tools.h"

/*******************************************************************\

Function: expr_eq

  Inputs:

 Outputs:

 Purpose: A method to detect equivalence between exprts that can
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
  exprt res;
  res.make_false();
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
  return res;
}

/*******************************************************************\

Function: get_quantifier_var_max

  Inputs:

 Outputs:

 Purpose: To obtain the max value for the quantifier variable
          of the specified forall/exists operator. The max variable 
          is in the form of "var_expr >= constant".

\*******************************************************************/

exprt get_quantifier_var_max(
  const exprt &var_expr,
  const exprt &quantifier_expr)
{
  exprt res;
  res.make_false();
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
  return res;
}

/*******************************************************************\

Function: instantiate(var_expr, var_inst, expr)

  Inputs:

 Outputs:

 Purpose: Replace all "var_expr"s inside "expr" with "var_inst"

\*******************************************************************/
void instantiate(
  const exprt &var_expr,
  const mp_integer &var_inst,
  exprt &expr)
{
  if(expr==var_expr)
  {
    expr=from_integer(var_inst, expr.type()); 
    return;
  }
  for(auto &x: expr.operands())
  {
    instantiate(var_expr, var_inst, x);
  }
}

/*******************************************************************\

Function: simplify_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_quantifier(exprt &expr)
{
  if(not(expr.id()==ID_forall or expr.id()==ID_exists))
    return false;
  assert(expr.operands().size()==2);
  assert(expr.op0().id()==ID_symbol);
  if(expr.op1().is_true() or expr.op1().is_false()) 
  {
    expr=expr.op1();
    return true;
  }

  bool result=true;
  exprt var_expr=expr.op0();
  /**
   * We need to rewrite the forall/exists quantifier into
   * an OR expr. 
   **/
  exprt re(expr);
  exprt tmp(re.op1());
  re.swap(tmp);
  exprt min_i=get_quantifier_var_min(var_expr, re);
  exprt max_i=get_quantifier_var_max(var_expr, re);
  exprt body_expr=re;
  if(var_expr.is_false() ||
     min_i.is_false() ||
     max_i.is_false() ||
     body_expr.is_false())
    return true;

  mp_integer lb, ub;
  to_integer(min_i, lb);
  to_integer(max_i, ub);

  if(lb>ub) return true;
  
  std::vector<exprt> expr_insts;
  for(mp_integer i=lb; i<=ub; ++i)
  {
    exprt constraint_expr=body_expr;
    instantiate(var_expr, i, constraint_expr);
    result=simplify_rec(constraint_expr);
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

  return result;

}


