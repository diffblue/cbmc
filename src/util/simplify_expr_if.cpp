/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "expr_util.h"
#include "range.h"
#include "std_expr.h"

bool simplify_exprt::simplify_if_implies(
  exprt &expr,
  const exprt &cond,
  bool truth,
  bool &new_truth)
{
  if(expr == cond)
  {
    new_truth = truth;
    return false;
  }

  if(truth && cond.id() == ID_lt && expr.id() == ID_lt)
  {
    const auto &cond_lt = to_binary_relation_expr(cond);
    const auto &expr_lt = to_binary_relation_expr(expr);

    if(
      cond_lt.op0() == expr_lt.op0() && cond_lt.op1().is_constant() &&
      expr_lt.op1().is_constant() &&
      cond_lt.op1().type() == expr_lt.op1().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond_lt.op1()), i1) &&
        !to_integer(to_constant_expr(expr_lt.op1()), i2))
      {
        if(i1 >= i2)
        {
          new_truth = true;
          return false;
        }
      }
    }

    if(
      cond_lt.op1() == expr_lt.op1() && cond_lt.op0().is_constant() &&
      expr_lt.op0().is_constant() &&
      cond_lt.op0().type() == expr_lt.op0().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond_lt.op0()), i1) &&
        !to_integer(to_constant_expr(expr_lt.op0()), i2))
      {
        if(i1 <= i2)
        {
          new_truth = true;
          return false;
        }
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_if_recursive(
  exprt &expr,
  const exprt &cond,
  bool truth)
{
  if(expr.type().id() == ID_bool)
  {
    bool new_truth;

    if(!simplify_if_implies(expr, cond, truth, new_truth))
    {
      if(new_truth)
      {
        expr = true_exprt();
        return false;
      }
      else
      {
        expr = false_exprt();
        return false;
      }
    }
  }

  bool no_change = true;

  Forall_operands(it, expr)
    no_change = simplify_if_recursive(*it, cond, truth) && no_change;

  return no_change;
}

bool simplify_exprt::simplify_if_conj(exprt &expr, const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr = true_exprt();
      return false;
    }
  }

  bool no_change = true;

  Forall_operands(it, expr)
    no_change = simplify_if_conj(*it, cond) && no_change;

  return no_change;
}

bool simplify_exprt::simplify_if_disj(exprt &expr, const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr = false_exprt();
      return false;
    }
  }

  bool no_change = true;

  Forall_operands(it, expr)
    no_change = simplify_if_disj(*it, cond) && no_change;

  return no_change;
}

bool simplify_exprt::simplify_if_branch(
  exprt &trueexpr,
  exprt &falseexpr,
  const exprt &cond)
{
  bool tno_change = true;
  bool fno_change = true;

  if(cond.id() == ID_and)
  {
    tno_change = simplify_if_conj(trueexpr, cond) && tno_change;
    fno_change = simplify_if_recursive(falseexpr, cond, false) && fno_change;
  }
  else if(cond.id() == ID_or)
  {
    tno_change = simplify_if_recursive(trueexpr, cond, true) && tno_change;
    fno_change = simplify_if_disj(falseexpr, cond) && fno_change;
  }
  else
  {
    tno_change = simplify_if_recursive(trueexpr, cond, true) && tno_change;
    fno_change = simplify_if_recursive(falseexpr, cond, false) && fno_change;
  }

  if(!tno_change)
    trueexpr = simplify_rec(trueexpr); // recursive call
  if(!fno_change)
    falseexpr = simplify_rec(falseexpr); // recursive call

  return tno_change && fno_change;
}

bool simplify_exprt::simplify_if_cond(exprt &expr)
{
  bool no_change = true;
  bool tmp = false;

  while(!tmp)
  {
    tmp = true;

    if(expr.id() == ID_and)
    {
      if(expr.has_operands())
      {
        exprt::operandst &operands = expr.operands();
        for(exprt::operandst::iterator it1 = operands.begin();
            it1 != operands.end();
            it1++)
        {
          for(exprt::operandst::iterator it2 = operands.begin();
              it2 != operands.end();
              it2++)
          {
            if(it1 != it2)
              tmp = simplify_if_recursive(*it1, *it2, true) && tmp;
          }
        }
      }
    }

    if(!tmp)
      expr = simplify_rec(expr); // recursive call

    no_change = tmp && no_change;
  }

  return no_change;
}

bool simplify_exprt::simplify_if_preorder(if_exprt &expr)
{
  exprt &cond = expr.cond();
  exprt &truevalue = expr.true_case();
  exprt &falsevalue = expr.false_case();

  bool no_change = true;

  // we first want to look at the condition
  auto r_cond = simplify_rec(cond);
  if(r_cond.has_changed())
  {
    cond = r_cond.expr;
    no_change = false;
  }

  // 1 ? a : b -> a  and  0 ? a : b -> b
  if(cond.is_constant())
  {
    exprt tmp = cond.is_true() ? truevalue : falsevalue;
    tmp = simplify_rec(tmp);
    expr.swap(tmp);
    return false;
  }

  if(do_simplify_if)
  {
    if(cond.id() == ID_not)
    {
      cond = to_not_expr(cond).op();
      truevalue.swap(falsevalue);
      no_change = false;
    }

#ifdef USE_LOCAL_REPLACE_MAP
    replace_mapt map_before(local_replace_map);

    // a ? b : c  --> a ? b[a/true] : c
    if(cond.id() == ID_and)
    {
      forall_operands(it, cond)
      {
        if(it->id() == ID_not)
          local_replace_map.insert(std::make_pair(it->op0(), false_exprt()));
        else
          local_replace_map.insert(std::make_pair(*it, true_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(cond, true_exprt()));

    auto r_truevalue = simplify_rec(truevalue);
    if(r_truevalue.has_changed())
    {
      truevalue = r_truevalue.expr;
      no_change = false;
    }

    local_replace_map = map_before;

    // a ? b : c  --> a ? b : c[a/false]
    if(cond.id() == ID_or)
    {
      forall_operands(it, cond)
      {
        if(it->id() == ID_not)
          local_replace_map.insert(std::make_pair(it->op0(), true_exprt()));
        else
          local_replace_map.insert(std::make_pair(*it, false_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(cond, false_exprt()));

    auto r_falsevalue = simplify_rec(falsevalue);
    if(r_falsevalue.has_changed())
    {
      falsevalue = r_falsevalue.expr;
      no_change = false;
    }

    local_replace_map.swap(map_before);
#else
    auto r_truevalue = simplify_rec(truevalue);
    if(r_truevalue.has_changed())
    {
      truevalue = r_truevalue.expr;
      no_change = false;
    }
    auto r_falsevalue = simplify_rec(falsevalue);
    if(r_falsevalue.has_changed())
    {
      falsevalue = r_falsevalue.expr;
      no_change = false;
    }
#endif
  }
  else
  {
    auto r_truevalue = simplify_rec(truevalue);
    if(r_truevalue.has_changed())
    {
      truevalue = r_truevalue.expr;
      no_change = false;
    }
    auto r_falsevalue = simplify_rec(falsevalue);
    if(r_falsevalue.has_changed())
    {
      falsevalue = r_falsevalue.expr;
      no_change = false;
    }
  }

  return no_change;
}

simplify_exprt::resultt<> simplify_exprt::simplify_if(const if_exprt &expr)
{
  const exprt &cond = expr.cond();
  const exprt &truevalue = expr.true_case();
  const exprt &falsevalue = expr.false_case();

  if(do_simplify_if)
  {
#if 0
    no_change = simplify_if_cond(cond) && no_change;
    no_change = simplify_if_branch(truevalue, falsevalue, cond) && no_change;
#endif

    if(expr.type() == bool_typet())
    {
      // a?b:c <-> (a && b) || (!a && c)

      if(truevalue.is_true() && falsevalue.is_false())
      {
        // a?1:0 <-> a
        return cond;
      }
      else if(truevalue.is_false() && falsevalue.is_true())
      {
        // a?0:1 <-> !a
        return changed(simplify_not(not_exprt(cond)));
      }
      else if(falsevalue.is_false())
      {
        // a?b:0 <-> a AND b
        return changed(simplify_node(and_exprt(cond, truevalue)));
      }
      else if(falsevalue.is_true())
      {
        // a?b:1 <-> !a OR b
        return changed(
          simplify_node(or_exprt(simplify_not(not_exprt(cond)), truevalue)));
      }
      else if(truevalue.is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        return changed(simplify_node(or_exprt(cond, falsevalue)));
      }
      else if(truevalue.is_false())
      {
        // a?0:b <-> !a && b
        return changed(
          simplify_node(and_exprt(simplify_not(not_exprt(cond)), falsevalue)));
      }
    }
  }

  if(truevalue == falsevalue)
    return truevalue;

  // this pushes the if-then-else into struct and array constructors
  if(
    ((truevalue.id() == ID_struct && falsevalue.id() == ID_struct) ||
     (truevalue.id() == ID_array && falsevalue.id() == ID_array)) &&
    truevalue.operands().size() == falsevalue.operands().size())
  {
    exprt cond_copy = cond;
    exprt falsevalue_copy = falsevalue;
    exprt truevalue_copy = truevalue;

    auto range_false = make_range(falsevalue_copy.operands());
    auto range_true = make_range(truevalue_copy.operands());
    auto new_expr = truevalue;
    new_expr.operands().clear();

    for(const auto &pair : range_true.zip(range_false))
    {
      new_expr.operands().push_back(
        simplify_if(if_exprt(cond_copy, pair.first, pair.second)));
    }

    return std::move(new_expr);
  }

  return unchanged(expr);
}
