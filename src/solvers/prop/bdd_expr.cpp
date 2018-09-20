/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

/// \file
/// Conversion between exprt and miniBDD

#include "bdd_expr.h"

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/format_expr.h>

#include <sstream>

mini_bddt bdd_exprt::from_expr_rec(const exprt &expr)
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

    mini_bddt op0=from_expr_rec(bin_expr.op0());
    mini_bddt op1=from_expr_rec(bin_expr.op1());

    return expr.id()==ID_and ? (op0&op1) :
           (expr.id()==ID_or ? (op0|op1) : (op0^op1));
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &imp_expr=to_implies_expr(expr);

    mini_bddt n_op0=!from_expr_rec(imp_expr.op0());
    mini_bddt op1=from_expr_rec(imp_expr.op1());

    return n_op0|op1;
  }
  else if(expr.id()==ID_equal &&
          expr.operands().size()==2 &&
          expr.op0().type().id()==ID_bool)
  {
    const equal_exprt &eq_expr=to_equal_expr(expr);

    mini_bddt op0=from_expr_rec(eq_expr.op0());
    mini_bddt op1=from_expr_rec(eq_expr.op1());

    return op0==op1;
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    mini_bddt cond=from_expr_rec(if_expr.cond());
    mini_bddt t_case=from_expr_rec(if_expr.true_case());
    mini_bddt f_case=from_expr_rec(if_expr.false_case());

    return ((!cond)|t_case)&(cond|f_case);
  }
  else
  {
    std::pair<expr_mapt::iterator, bool> entry=
      expr_map.insert(std::make_pair(expr, mini_bddt()));

    if(entry.second)
    {
      std::ostringstream s;
      s << format(expr);
      entry.first->second=bdd_mgr.Var(s.str());

      node_map.insert(std::make_pair(entry.first->second.var(),
                                     expr));
    }

    return entry.first->second;
  }
}

void bdd_exprt::from_expr(const exprt &expr)
{
  root=from_expr_rec(expr);
}

exprt bdd_exprt::as_expr(const mini_bddt &r) const
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
    if(r.low().is_true())
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

exprt bdd_exprt::as_expr() const
{
  if(!root.is_initialized())
    return nil_exprt();

  return as_expr(root);
}
