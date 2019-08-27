/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

/// \file
/// Conversion between exprt and miniBDD

#include "bdd_expr.h"
#include "bdd_strategy.h"
#include "literal.h"
#include "literal_expr.h"
#include "prop_conv_solver.h"

#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/std_expr.h>

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

/// Disjunction of two expressions. If the second is already an `or_exprt`
/// add to its operands instead of creating a new expression.
static exprt make_or(exprt a, exprt b)
{
  if(b.id() == ID_or)
  {
    b.add_to_operands(std::move(a));
    return b;
  }
  return or_exprt{std::move(a), std::move(b)};
}

/// Helper function for \c bddt to \c exprt conversion
/// \param r: node to convert
/// \param cache: map of already computed values
exprt bdd_exprt::as_expr(
  const bdd_nodet &r,
  std::unordered_map<bdd_nodet::idt, exprt> &cache) const
{
  if(r.is_constant())
  {
    if(r.is_complement())
      return false_exprt();
    else
      return true_exprt();
  }

  auto index = narrow<std::size_t>(r.index());
  INVARIANT(index < node_map.size(), "Index should be in node_map");
  const exprt &n_expr = node_map[index];

  // Look-up cache for already computed value
  auto insert_result = cache.emplace(r.id(), nil_exprt());
  if(insert_result.second)
  {
    auto result_ignoring_complementation = [&]() -> exprt {
      if(r.else_branch().is_constant())
      {
        if(r.then_branch().is_constant())
        {
          if(r.else_branch().is_complement()) // else is false
            return n_expr;
          return not_exprt(n_expr); // else is true
        }
        else
        {
          if(r.else_branch().is_complement()) // else is false
          {
            exprt then_case = as_expr(r.then_branch(), cache);
            return make_and(n_expr, then_case);
          }
          exprt then_case = as_expr(r.then_branch(), cache);
          return make_or(not_exprt(n_expr), then_case);
        }
      }
      else if(r.then_branch().is_constant())
      {
        if(r.then_branch().is_complement()) // then is false
        {
          exprt else_case = as_expr(r.else_branch(), cache);
          return make_and(not_exprt(n_expr), else_case);
        }
        exprt else_case = as_expr(r.else_branch(), cache);
        return make_or(n_expr, else_case);
      }

      exprt then_branch = as_expr(r.then_branch(), cache);
      exprt else_branch = as_expr(r.else_branch(), cache);
      return if_exprt(n_expr, then_branch, else_branch);
    }();

    insert_result.first->second =
      r.is_complement()
        ? boolean_negate(std::move(result_ignoring_complementation))
        : result_ignoring_complementation;
  }
  return insert_result.first->second;
}

exprt bdd_exprt::as_expr(const bddt &root) const
{
  std::unordered_map<bdd_nodet::idt, exprt> cache;
  bdd_nodet node = bdd_mgr.bdd_node(root);
  return as_expr(node, cache);
}

/// Internal state of the strategy to convert BDD nodes to solver literals
struct handle_guard_strategyt
{
  const std::vector<exprt> &node_map;
  decision_proceduret &solver;
};

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::leaf(
  const bdd_nodet::indext &index)
{
  return internal_state.solver.handle(internal_state.node_map[index]);
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_false()
{
  return internal_state.solver.handle(false_exprt{});
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_true()
{
  return internal_state.solver.handle(true_exprt{});
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_not(const exprt &l1)
{
  return not_exprt{l1};
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_and(
  const exprt &l1,
  const exprt &l2)
{
  return internal_state.solver.handle(and_exprt{l1, l2});
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_or(
  const exprt &l1,
  const exprt &l2)
{
  return internal_state.solver.handle(or_exprt{l1, l2});
}

template <>
exprt bdd_strategyt<exprt, handle_guard_strategyt>::make_if_then_else(
  const exprt &i,
  const exprt &t,
  const exprt &e)
{
  return make_or(make_and(i, t), make_and(not_exprt{i}, e));
}

exprt bdd_exprt::as_solver_literal(decision_proceduret &solver, const bddt &bdd)
  const
{
  bdd_strategyt<exprt, handle_guard_strategyt> strategy{
    handle_guard_strategyt{node_map, solver}};
  return strategy.apply(bdd_mgr.bdd_node(bdd));
}
