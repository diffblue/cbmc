/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include <unordered_set>

#include "expr.h"
#include "expr_util.h"
#include "invariant.h"
#include "mathematical_expr.h"
#include "namespace.h"
#include "std_expr.h"

simplify_exprt::resultt<> simplify_exprt::simplify_boolean(const exprt &expr)
{
  if(!expr.has_operands())
    return unchanged(expr);

  const exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool)
    return unchanged(expr);

  if(expr.id()==ID_implies)
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
    {
      return unchanged(expr);
    }

    // turn a => b into !a || b

    expr.id(ID_or);
    expr.op0() = boolean_negate(expr.op0());
    simplify_node(expr.op0());
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_xor)
  {
    bool no_change = true;

    bool negate=false;

    for(exprt::operandst::const_iterator it=operands.begin();
        it!=operands.end();)
    {
      if(it->type().id()!=ID_bool)
        return unchanged(expr);

      bool erase;

      if(it->is_true())
      {
        erase=true;
        negate=!negate;
      }
      else
        erase=it->is_false();

      if(erase)
      {
        it=operands.erase(it);
        no_change = false;
      }
      else
        it++;
    }

    if(operands.empty())
    {
      return make_boolean_expr(negate);
    }
    else if(operands.size()==1)
    {
      exprt tmp(operands.front());
      if(negate)
        tmp = boolean_negate(operands.front());
      return std::move(tmp);
    }

    return no_change;
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    std::unordered_set<exprt, irep_hash> expr_set;

    bool no_change = true;

    for(exprt::operandst::const_iterator it=operands.begin();
        it!=operands.end();)
    {
      if(it->type().id()!=ID_bool)
        return unchanged(expr);

      bool is_true=it->is_true();
      bool is_false=it->is_false();

      if(expr.id()==ID_and && is_false)
      {
        return false_exprt();
      }
      else if(expr.id()==ID_or && is_true)
      {
        return true_exprt();
      }

      bool erase=
        (expr.id()==ID_and ? is_true : is_false) ||
        !expr_set.insert(*it).second;

      if(erase)
      {
        it=operands.erase(it);
        no_change = false;
      }
      else
        it++;
    }

    // search for a and !a
    for(const exprt &op : operands)
      if(op.id()==ID_not &&
         op.operands().size()==1 &&
         op.type().id()==ID_bool &&
         expr_set.find(op.op0())!=expr_set.end())
      {
        return make_boolean_expr(expr.id() == ID_or);
      }

    if(operands.empty())
    {
      return make_boolean_expr(expr.id() == ID_and);
    }
    else if(operands.size()==1)
    {
      return operands.front();
    }

    return no_change;
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_not(const exprt &expr)
{
  if(expr.operands().size()!=1)
    return unchanged(expr);

  const exprt &op=expr.op0();

  if(expr.type().id()!=ID_bool ||
     op.type().id()!=ID_bool)
  {
    return unchanged(expr);
  }

  if(op.id()==ID_not) // (not not a) == a
  {
    if(op.operands().size()==1)
      return op.op0();
  }
  else if(op.is_false())
  {
    return true_exprt();
  }
  else if(op.is_true())
  {
    return false_exprt();
  }
  else if(op.id()==ID_and ||
          op.id()==ID_or)
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);

    Forall_operands(it, expr)
    {
      *it = boolean_negate(*it);
      simplify_node(*it);
    }

    expr.id(expr.id()==ID_and?ID_or:ID_and);

    return false;
  }
  else if(op.id()==ID_notequal) // !(a!=b) <-> a==b
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);
    expr.id(ID_equal);
    return false;
  }
  else if(op.id()==ID_exists) // !(exists: a) <-> forall: not a
  {
    auto const &op_as_exists = to_exists_expr(op);
    forall_exprt rewritten_op(
      op_as_exists.symbol(), not_exprt(op_as_exists.where()));
    simplify_node(rewritten_op.where());
    return std::move(rewritten_op);
  }
  else if(op.id() == ID_forall) // !(forall: a) <-> exists: not a
  {
    auto const &op_as_forall = to_forall_expr(op);
    exists_exprt rewritten_op(
      op_as_forall.symbol(), not_exprt(op_as_forall.where()));
    simplify_node(rewritten_op.where());
    return std::move(rewritten_op);
  }

  return unchanged(expr);
}
