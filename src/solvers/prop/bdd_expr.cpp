/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

/// \file
/// Conversion between exprt and miniBDD

#include "bdd_expr.h"

#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/std_expr.h>

#include <sstream>

bddt bdd_exprt::from_expr_rec(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  if(expr.is_constant())
    return expr.is_false() ? bdd_mgr.bdd_false() : bdd_mgr.bdd_true();
  else if(expr.id()==ID_not)
    return from_expr_rec(to_not_expr(expr).op()).bdd_not();
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions have at least two operands");
    exprt bin_expr=make_binary(expr);

    bddt op0 = from_expr_rec(bin_expr.op0());
    bddt op1 = from_expr_rec(bin_expr.op1());

    return expr.id() == ID_and
             ? op0.bdd_and(op1)
             : (expr.id() == ID_or ? op0.bdd_or(op1) : op0.bdd_xor(op1));
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &imp_expr=to_implies_expr(expr);

    bddt n_op0 = from_expr_rec(imp_expr.op0()).bdd_not();
    bddt op1 = from_expr_rec(imp_expr.op1());

    return n_op0.bdd_or(op1);
  }
  else if(expr.id()==ID_equal &&
          expr.operands().size()==2 &&
          expr.op0().type().id()==ID_bool)
  {
    const equal_exprt &eq_expr=to_equal_expr(expr);

    bddt op0 = from_expr_rec(eq_expr.op0());
    bddt op1 = from_expr_rec(eq_expr.op1());

    return op0.bdd_xor(op1).bdd_not();
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    bddt cond = from_expr_rec(if_expr.cond());
    bddt t_case = from_expr_rec(if_expr.true_case());
    bddt f_case = from_expr_rec(if_expr.false_case());

    return bddt::bdd_ite(cond, t_case, f_case);
  }
  else
  {
    std::pair<expr_mapt::iterator, bool> entry =
      expr_map.emplace(expr, bdd_mgr.bdd_true());

    if(entry.second)
    {
      node_map.push_back(expr);
      const unsigned index = (unsigned)node_map.size() - 1;
      entry.first->second = bdd_mgr.bdd_variable(index);
    }

    return entry.first->second;
  }
}

bddt bdd_exprt::from_expr(const exprt &expr)
{
  return from_expr_rec(expr);
}

/// Helper function for \c bddt to \c exprt conversion
/// \param r: node to convert
/// \param complement: whether we want the negation of the expression
///        represented by r
/// \param cache: map of already computed values
exprt bdd_exprt::as_expr(
  const bdd_nodet &r,
  bool complement,
  std::unordered_map<bdd_nodet::idt, exprt> &cache) const
{
  if(r.is_constant())
  {
    if(complement)
      return false_exprt();
    else
      return true_exprt();
  }

  INVARIANT(r.index() < node_map.size(), "Index should be in node_map");
  const exprt &n_expr = node_map[r.index()];

  // Look-up cache for already computed value
  auto insert_result = cache.emplace(r.id(), nil_exprt());
  if(insert_result.second)
  {
    insert_result.first->second = [&]() -> exprt {
      if(r.else_branch().is_constant())
      {
        if(r.then_branch().is_constant())
        {
          if(r.else_branch().is_complement() != complement)
            return n_expr;
          return not_exprt(n_expr);
        }
        else
        {
          if(r.else_branch().is_complement() != complement)
          {
            return and_exprt(
              n_expr,
              as_expr(
                r.then_branch(),
                complement != r.then_branch().is_complement(),
                cache));
          }
          return or_exprt(
            not_exprt(n_expr),
            as_expr(
              r.then_branch(),
              complement != r.then_branch().is_complement(),
              cache));
        }
      }
      else if(r.then_branch().is_constant())
      {
        if(r.then_branch().is_complement() != complement)
        {
          return and_exprt(
            not_exprt(n_expr),
            as_expr(
              r.else_branch(),
              complement != r.else_branch().is_complement(),
              cache));
        }
        return or_exprt(
          n_expr,
          as_expr(
            r.else_branch(),
            complement != r.else_branch().is_complement(),
            cache));
      }
      return if_exprt(
        n_expr,
        as_expr(
          r.then_branch(),
          r.then_branch().is_complement() != complement,
          cache),
        as_expr(
          r.else_branch(),
          r.else_branch().is_complement() != complement,
          cache));
    }();
  }
  return insert_result.first->second;
}

exprt bdd_exprt::as_expr(const bddt &root) const
{
  std::unordered_map<bdd_nodet::idt, exprt> cache;
  bdd_nodet node = bdd_mgr.bdd_node(root);
  return as_expr(node, node.is_complement(), cache);
}
