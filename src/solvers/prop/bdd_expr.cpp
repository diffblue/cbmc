/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

#include <langapi/language_util.h>

#include <util/std_expr.h>
#include <util/expr_util.h>

#include "bdd_expr.h"

/*******************************************************************\

Function: bdd_exprt::from_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_exprt::BDDt bdd_exprt::from_expr_rec(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  if(expr.is_constant())
    return expr.is_false() ? bdd_mgr.False() : bdd_mgr.True();
  else if(expr.id()==ID_not)
    return !from_expr_rec(to_not_expr(expr).op());
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    assert(expr.operands().size()>=2);
    exprt bin_expr=make_binary(expr);

    bdd_exprt::BDDt op0=from_expr_rec(bin_expr.op0());
    bdd_exprt::BDDt op1=from_expr_rec(bin_expr.op1());

    return expr.id()==ID_and ? (op0&op1) :
           (expr.id()==ID_or ? (op0|op1) : (op0^op1));
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &imp_expr=to_implies_expr(expr);

    bdd_exprt::BDDt n_op0=!from_expr_rec(imp_expr.op0());
    bdd_exprt::BDDt op1=from_expr_rec(imp_expr.op1());

    return n_op0|op1;
  }
  else if(expr.id()==ID_equal &&
          expr.operands().size()==2 &&
          expr.op0().type().id()==ID_bool)
  {
    const equal_exprt &eq_expr=to_equal_expr(expr);

    bdd_exprt::BDDt op0=from_expr_rec(eq_expr.op0());
    bdd_exprt::BDDt op1=from_expr_rec(eq_expr.op1());

    return op0==op1;
  }
  else if(expr.id()==ID_iff)
  {
    assert(expr.operands().size()==2);

    bdd_exprt::BDDt op0=from_expr_rec(expr.op0());
    bdd_exprt::BDDt op1=from_expr_rec(expr.op1());

    return op0==op1;
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    bdd_exprt::BDDt cond=from_expr_rec(if_expr.cond());
    bdd_exprt::BDDt t_case=from_expr_rec(if_expr.true_case());
    bdd_exprt::BDDt f_case=from_expr_rec(if_expr.false_case());

    return ((!cond)|t_case)&(cond|f_case);
  }
  else
  {
    std::pair<expr_mapt::iterator, bool> entry=
      expr_map.insert(std::make_pair(expr, bdd_exprt::BDDt()));

    if(entry.second)
    {
      std::string s=::from_expr(ns, "", expr);
      entry.first->second=bdd_mgr.Var(s);

      node_map.insert(std::make_pair(entry.first->second.var(),
                                     expr));
    }

    return entry.first->second;
  }
}

/*******************************************************************\

Function: bdd_exprt::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_exprt::from_expr(const exprt &expr)
{
  root=from_expr_rec(expr);
}

/*******************************************************************\

Function: bdd_exprt::as_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bdd_exprt::as_expr(const bdd_exprt::BDDt &r) const
{
  if(r.is_constant())
  {
    if(r.is_true())
      return true_exprt();
    else
      return false_exprt();
  }

  node_mapt::const_iterator entry=node_map.find(r.var());
  assert(entry!=node_map.end());
  const exprt &n_expr=entry->second;

  if(r.low().is_false())
  {
    if(r.high().is_true())
      return n_expr;
    else
      return and_exprt(n_expr, as_expr(r.high()));
  }
  else if(r.high().is_false())
  {
    if(r.high().is_true())
      return not_exprt(n_expr);
    else
      return and_exprt(not_exprt(n_expr), as_expr(r.low()));
  }
  else if(r.low().is_true())
    return or_exprt(not_exprt(n_expr), as_expr(r.high()));
  else if(r.high().is_true())
    return or_exprt(n_expr, as_expr(r.low()));
  else
    return if_exprt(n_expr, as_expr(r.high()), as_expr(r.low()));
}

/*******************************************************************\

Function: bdd_exprt::as_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bdd_exprt::as_expr() const
{
  if(!root.is_initialized())
    return nil_exprt();

  return as_expr(root);
}

