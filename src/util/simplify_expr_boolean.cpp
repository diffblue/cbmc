/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include <cassert>
#include <unordered_set>

#include "expr.h"
#include "namespace.h"
#include "std_expr.h"

bool simplify_exprt::simplify_boolean(exprt &expr)
{
  if(!expr.has_operands())
    return true;

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool)
    return true;

  if(expr.id()==ID_implies)
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;

    // turn a => b into !a || b

    expr.id(ID_or);
    expr.op0().make_not();
    simplify_node(expr.op0());
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_iff)
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;

    if(operands.front().is_false())
    {
      expr.id(ID_not);
      operands.erase(operands.begin());
      return false;
    }
    else if(operands.front().is_true())
    {
      exprt tmp(operands.back());
      expr.swap(tmp);
      return false;
    }
    else if(operands.back().is_false())
    {
      expr.id(ID_not);
      operands.erase(++operands.begin());
      return false;
    }
    else if(operands.back().is_true())
    {
      exprt tmp(operands.front());
      expr.swap(tmp);
      return false;
    }
  }
  else if(expr.id() == ID_xor)
  {
    bool result=true;

    bool negate=false;

    for(exprt::operandst::const_iterator it = operands.begin();
        it != operands.end();)
    {
      if(it->type().id() != ID_bool)
        return true;

      if(it->is_true())
        negate = !negate;

      if(it->is_constant())
      {
        it = operands.erase(it);
        result = false;
      }
      else
        it++;
    }

    if(operands.empty())
    {
      expr.make_bool(negate);
      return false;
    }
    else if(operands.size() == 1)
    {
      exprt tmp(operands.front());
      if(negate)
        tmp.make_not();
      expr.swap(tmp);
      return false;
    }

    return result;
  }
  else if(expr.id() == ID_and || expr.id() == ID_or)
  {
    std::unordered_set<exprt, irep_hash> expr_set;

    bool result = true;

    for(exprt::operandst::const_iterator it = operands.begin();
        it != operands.end();)
    {
      if(it->type().id()!=ID_bool)
        return true;

      bool is_true=it->is_true();
      bool is_false=it->is_false();

      if(expr.id()==ID_and && is_false)
      {
        expr=false_exprt();
        return false;
      }
      else if(expr.id()==ID_or && is_true)
      {
        expr=true_exprt();
        return false;
      }

      bool erase = (expr.id() == ID_and ? is_true : is_false) ||
                   !expr_set.insert(*it).second;

      if(erase)
      {
        it=operands.erase(it);
        result=false;
      }
      else
        it++;
    }

    // search for a and !a
    for(const exprt &op : operands)
      if(
        op.id() == ID_not && op.operands().size() == 1 &&
        op.type().id() == ID_bool && expr_set.find(op.op0()) != expr_set.end())
      {
        expr.make_bool(expr.id() == ID_or);
        return false;
      }

    if(operands.empty())
    {
      expr.make_bool(expr.id() == ID_and);
      return false;
    }
    else if(operands.size()==1)
    {
      exprt tmp(operands.front());
      expr.swap(tmp);
      return false;
    }

    return result;
  }

  return true;
}

bool simplify_exprt::simplify_not(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &op=expr.op0();

  if(expr.type().id()!=ID_bool ||
     op.type().id()!=ID_bool)
    return true;

  if(op.id()==ID_not) // (not not a) == a
  {
    if(op.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(op.op0());
      expr.swap(tmp);
      return false;
    }
  }
  else if(op.is_false())
  {
    expr=true_exprt();
    return false;
  }
  else if(op.is_true())
  {
    expr=false_exprt();
    return false;
  }
  else if(op.id()==ID_and ||
          op.id()==ID_or)
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);

    Forall_operands(it, expr)
    {
      it->make_not();
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
    assert(op.operands().size()==2);
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);
    expr.id(ID_forall);
    expr.op1().make_not();
    simplify_node(expr.op1());
    return false;
  }

  return true;
}
