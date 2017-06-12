/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <unordered_set>

#include "simplify_expr_class.h"
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
  else if(expr.id()==ID_or ||
          expr.id()==ID_and ||
          expr.id()==ID_xor)
  {
    if(operands.empty())
      return true;

    bool result=true;

    exprt::operandst::const_iterator last;
    bool last_set=false;

    bool negate=false;

    for(exprt::operandst::iterator it=operands.begin();
        it!=operands.end();)
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

      bool erase;

      if(expr.id()==ID_and)
        erase=is_true;
      else if(is_true && expr.id()==ID_xor)
      {
        erase=true;
        negate=!negate;
      }
      else
        erase=is_false;

      if(last_set && *it==*last &&
         (expr.id()==ID_or || expr.id()==ID_and))
        erase=true; // erase duplicate operands

      if(erase)
      {
        it=operands.erase(it);
        result=false;
      }
      else
      {
        last=it;
        last_set=true;
        it++;
      }
    }

    // search for a and !a
    if(expr.id()==ID_and || expr.id()==ID_or)
    {
      // first gather all the a's with !a

      std::unordered_set<exprt, irep_hash> expr_set;

      forall_operands(it, expr)
        if(it->id()==ID_not &&
           it->operands().size()==1 &&
           it->type().id()==ID_bool)
          expr_set.insert(it->op0());

      // now search for a

      if(!expr_set.empty())
      {
        forall_operands(it, expr)
        {
          if(it->id()!=ID_not &&
             expr_set.find(*it)!=expr_set.end())
          {
            expr.make_bool(expr.id()==ID_or);
            return false;
          }
        }
      }
    }

    if(operands.empty())
    {
      if(expr.id()==ID_and || negate)
        expr=true_exprt();
      else
        expr=false_exprt();

      return false;
    }
    else if(operands.size()==1)
    {
      if(negate)
        expr.op0().make_not();
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
