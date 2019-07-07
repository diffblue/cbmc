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
    if(
      cond.op0() == expr.op0() && cond.op1().is_constant() &&
      expr.op1().is_constant() && cond.op1().type() == expr.op1().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond.op1()), i1) &&
        !to_integer(to_constant_expr(expr.op1()), i2))
      {
        if(i1 >= i2)
        {
          new_truth = true;
          return false;
        }
      }
    }

    if(
      cond.op1() == expr.op1() && cond.op0().is_constant() &&
      expr.op0().is_constant() && cond.op0().type() == expr.op0().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond.op0()), i1) &&
        !to_integer(to_constant_expr(expr.op0()), i2))
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

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_recursive(*it, cond, truth) && result;

  return result;
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

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_conj(*it, cond) && result;

  return result;
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

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_disj(*it, cond) && result;

  return result;
}

bool simplify_exprt::simplify_if_branch(
  exprt &trueexpr,
  exprt &falseexpr,
  const exprt &cond)
{
  bool tresult = true;
  bool fresult = true;

  if(cond.id() == ID_and)
  {
    tresult = simplify_if_conj(trueexpr, cond) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }
  else if(cond.id() == ID_or)
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_disj(falseexpr, cond) && fresult;
  }
  else
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }

  if(!tresult)
    trueexpr = simplify_rec(trueexpr); // recursive call
  if(!fresult)
    falseexpr = simplify_rec(falseexpr); // recursive call

  return tresult && fresult;
}

bool simplify_exprt::simplify_if_cond(exprt &expr)
{
  bool result = true;
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

    result = tmp && result;
  }

  return result;
}

bool simplify_exprt::simplify_if_preorder(if_exprt &expr)
{
  exprt &cond = expr.cond();
  exprt &truevalue = expr.true_case();
  exprt &falsevalue = expr.false_case();

  bool result = true;

  // we first want to look at the condition
  auto r_cond = simplify_rec(cond);
  if(r_cond.has_changed())
  {
    cond = r_cond.expr;
    result = false;
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
      exprt tmp;
      tmp.swap(cond.op0());
      cond.swap(tmp);
      truevalue.swap(falsevalue);
      result = false;
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
      result = false;
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
      result = false;
    }

    local_replace_map.swap(map_before);
#else
    auto r_truevalue = simplify_rec(truevalue);
    if(r_truevalue.has_changed())
    {
      truevalue = r_truevalue.expr;
      result = false;
    }
    auto r_falsevalue = simplify_rec(falsevalue);
    if(r_falsevalue.has_changed())
    {
      falsevalue = r_falsevalue.expr;
      result = false;
    }
#endif
  }
  else
  {
    auto r_truevalue = simplify_rec(truevalue);
    if(r_truevalue.has_changed())
    {
      truevalue = r_truevalue.expr;
      result = false;
    }
    auto r_falsevalue = simplify_rec(falsevalue);
    if(r_falsevalue.has_changed())
    {
      falsevalue = r_falsevalue.expr;
      result = false;
    }
  }

  return result;
}

simplify_exprt::resultt<> simplify_exprt::simplify_if(const if_exprt &expr)
{
  const exprt &cond = expr.cond();
  const exprt &truevalue = expr.true_case();
  const exprt &falsevalue = expr.false_case();

  if(do_simplify_if)
  {
#if 0
    result = simplify_if_cond(cond) && result;
    result = simplify_if_branch(truevalue, falsevalue, cond) && result;
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
        exprt tmp = boolean_negate(cond);
        simplify_node(tmp);
        return std::move(tmp);
      }
      else if(falsevalue.is_false())
      {
        // a?b:0 <-> a AND b
        and_exprt tmp(cond, truevalue);
        simplify_node(tmp);
        return std::move(tmp);
      }
      else if(falsevalue.is_true())
      {
        // a?b:1 <-> !a OR b
        exprt tmp_not_cond = boolean_negate(cond);
        simplify_node(tmp_not_cond);
        or_exprt tmp(tmp_not_cond, truevalue);
        simplify_node(tmp);
        return std::move(tmp);
      }
      else if(truevalue.is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        or_exprt tmp(cond, falsevalue);
        simplify_node(tmp);
        return std::move(tmp);
      }
      else if(truevalue.is_false())
      {
        // a?0:b <-> !a && b
        exprt tmp_not_cond = boolean_negate(cond);
        simplify_node(tmp_not_cond);
        and_exprt tmp(tmp_not_cond, falsevalue);
        simplify_node(tmp);
        return std::move(tmp);
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
