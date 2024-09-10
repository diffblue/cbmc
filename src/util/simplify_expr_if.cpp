/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
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
  if(expr.is_boolean())
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
  for(const auto &op : cond.operands())
  {
    if(expr == op)
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
  for(const auto &op : cond.operands())
  {
    if(expr == op)
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

static simplify_exprt::resultt<> build_if_expr(
  const if_exprt &expr,
  simplify_exprt::resultt<> cond,
  simplify_exprt::resultt<> truevalue,
  simplify_exprt::resultt<> falsevalue)
{
  if(
    !cond.has_changed() && !truevalue.has_changed() &&
    !falsevalue.has_changed())
  {
    return simplify_exprt::resultt<>(
      simplify_exprt::resultt<>::UNCHANGED, expr);
  }
  else
  {
    if_exprt result = expr;
    if(cond.has_changed())
      result.cond() = std::move(cond.expr);
    if(truevalue.has_changed())
      result.true_case() = std::move(truevalue.expr);
    if(falsevalue.has_changed())
      result.false_case() = std::move(falsevalue.expr);
    return result;
  }
}

simplify_exprt::resultt<>
simplify_exprt::simplify_if_preorder(const if_exprt &expr)
{
  const exprt &cond = expr.cond();
  const exprt &truevalue = expr.true_case();
  const exprt &falsevalue = expr.false_case();

  // we first want to look at the condition
  auto r_cond = simplify_rec(cond);

  // 1 ? a : b -> a  and  0 ? a : b -> b
  if(r_cond.expr.is_constant())
  {
    return changed(simplify_rec(
      to_constant_expr(r_cond.expr).is_true() ? truevalue : falsevalue));
  }

  if(do_simplify_if)
  {
    bool swap_branches = false;

    if(r_cond.expr.id() == ID_not)
    {
      r_cond = changed(to_not_expr(r_cond.expr).op());
      swap_branches = true;
    }

#ifdef USE_LOCAL_REPLACE_MAP
    replace_mapt map_before(local_replace_map);

    // a ? b : c  --> a ? b[a/true] : c
    if(r_cond.expr.id() == ID_and)
    {
      for(const auto &op : r_cond.expr.operands())
      {
        if(op.id() == ID_not)
          local_replace_map.insert(std::make_pair(op.op0(), false_exprt()));
        else
          local_replace_map.insert(std::make_pair(op, true_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(r_cond.expr, true_exprt()));

    auto r_truevalue = simplify_rec(swap_branches ? falsevalue : truevalue);

    local_replace_map = map_before;

    // a ? b : c  --> a ? b : c[a/false]
    if(r_cond.expr.id() == ID_or)
    {
      for(const auto &op : r_cond.expr.operands())
      {
        if(op.id() == ID_not)
          local_replace_map.insert(std::make_pair(op.op0(), true_exprt()));
        else
          local_replace_map.insert(std::make_pair(op, false_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(r_cond.expr, false_exprt()));

    auto r_falsevalue = simplify_rec(swap_branches ? truevalue : falsevalue);

    local_replace_map.swap(map_before);

    if(swap_branches)
    {
      // tell build_if_expr to replace truevalue and falsevalue
      r_truevalue.expr_changed = CHANGED;
      r_falsevalue.expr_changed = CHANGED;
    }
    return build_if_expr(expr, r_cond, r_truevalue, r_falsevalue);
#else
    if(!swap_branches)
    {
      return build_if_expr(
        expr, r_cond, simplify_rec(truevalue), simplify_rec(falsevalue));
    }
    else
    {
      return build_if_expr(
        expr,
        r_cond,
        changed(simplify_rec(falsevalue)),
        changed(simplify_rec(truevalue)));
    }
#endif
  }
  else
  {
    return build_if_expr(
      expr, r_cond, simplify_rec(truevalue), simplify_rec(falsevalue));
  }
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

      if(
        truevalue.is_constant() && to_constant_expr(truevalue).is_true() &&
        falsevalue.is_constant() && to_constant_expr(falsevalue).is_false())
      {
        // a?1:0 <-> a
        return cond;
      }
      else if(
        truevalue.is_constant() && to_constant_expr(truevalue).is_false() &&
        falsevalue.is_constant() && to_constant_expr(falsevalue).is_true())
      {
        // a?0:1 <-> !a
        return changed(simplify_not(not_exprt(cond)));
      }
      else if(
        falsevalue.is_constant() && to_constant_expr(falsevalue).is_false())
      {
        // a?b:0 <-> a AND b
        return changed(simplify_boolean(and_exprt(cond, truevalue)));
      }
      else if(
        falsevalue.is_constant() && to_constant_expr(falsevalue).is_true())
      {
        // a?b:1 <-> !a OR b
        return changed(
          simplify_boolean(or_exprt(simplify_not(not_exprt(cond)), truevalue)));
      }
      else if(truevalue.is_constant() && to_constant_expr(truevalue).is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        return changed(simplify_boolean(or_exprt(cond, falsevalue)));
      }
      else if(truevalue.is_constant() && to_constant_expr(truevalue).is_false())
      {
        // a?0:b <-> !a && b
        return changed(simplify_boolean(
          and_exprt(simplify_not(not_exprt(cond)), falsevalue)));
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
