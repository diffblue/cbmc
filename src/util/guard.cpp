/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "std_expr.h"
#include "simplify_utils.h"
#include "guard.h"

/*******************************************************************\

Function: guardt::as_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guardt::guard_expr(exprt &dest) const
{
  if(is_true())
  {
    // do nothing
  }
  else
  {
    if(dest.is_false())
    {
      dest=as_expr();
      dest.make_not();
    }
    else
    {
      implies_exprt tmp;
      tmp.op0()=as_expr();
      tmp.op1().swap(dest);
      dest.swap(tmp);
    }
  }
}

#if 0
/*******************************************************************\

Function: guardt::as_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt guardt::as_expr(guard_listt::const_iterator it) const
{
  if(it==guard_list.end())
    return true_exprt();
  else if(it==--guard_list.end())
    return guard_list.back();

  exprt dest;
  dest=exprt(ID_and, typet(ID_bool));
  dest.reserve_operands(guard_list.size());
  for(; it!=guard_list.end(); it++)
  {
    if(!it->is_boolean())
      throw "guard is expected to be Boolean";
    dest.copy_to_operands(*it);
  }

  return dest;
}
#endif

/*******************************************************************\

Function: guardt::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guardt::add(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  if(is_false() || expr.is_true())
    return;
  else if(is_true() || expr.is_false())
  {
    *this=expr;

    return;
  }
  else if(id()!=ID_and)
  {
    and_exprt a;
    a.copy_to_operands(*this);
    *this=a;
  }

  operandst &op=operands();

  if(expr.id()==ID_and)
    op.insert(op.end(),
              expr.operands().begin(),
              expr.operands().end());
  else
    op.push_back(expr);
}

/*******************************************************************\

Function: operator -=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

guardt &operator -= (guardt &g1, const guardt &g2)
{
  if(g1.id()!=ID_and || g2.id()!=ID_and)
    return g1;

  sort_and_join(g1);
  guardt g2_sorted=g2;
  sort_and_join(g2_sorted);

  exprt::operandst &op1=g1.operands();
  const exprt::operandst &op2=g2_sorted.operands();

  exprt::operandst::iterator it1=op1.begin();
  for(exprt::operandst::const_iterator
      it2=op2.begin();
      it2!=op2.end();
      ++it2)
  {
    while(it1!=op1.end() && *it1<*it2)
      ++it1;
    if(it1!=op1.end() && *it1==*it2)
      it1=op1.erase(it1);
  }

  g1=conjunction(op1);

  return g1;
}

/*******************************************************************\

Function: operator |=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

guardt &operator |= (guardt &g1, const guardt &g2)
{
  if(g2.is_false() || g1.is_true()) return g1;
  if(g1.is_false() || g2.is_true()) { g1=g2; return g1; }

  if(g1.id()!=ID_and || g2.id()!=ID_and)
  {
    exprt tmp(g2);
    tmp.make_not();

    if(tmp==g1)
      g1.make_true();
    else
      g1=or_exprt(g1, g2);

    // TODO: make simplify more capable and apply here

    return g1;
  }

  // find common prefix
  sort_and_join(g1);
  guardt g2_sorted=g2;
  sort_and_join(g2_sorted);

  exprt::operandst &op1=g1.operands();
  const exprt::operandst &op2=g2_sorted.operands();

  exprt::operandst n_op1, n_op2;
  n_op1.reserve(op1.size());
  n_op2.reserve(op2.size());

  exprt::operandst::iterator it1=op1.begin();
  for(exprt::operandst::const_iterator
      it2=op2.begin();
      it2!=op2.end();
      ++it2)
  {
    while(it1!=op1.end() && *it1<*it2)
    {
      n_op1.push_back(*it1);
      it1=op1.erase(it1);
    }
    if(it1!=op1.end() && *it1==*it2)
      ++it1;
    else
      n_op2.push_back(*it2);
  }
  while(it1!=op1.end())
  {
    n_op1.push_back(*it1);
    it1=op1.erase(it1);
  }

  if(n_op2.empty()) return g1;

  // end of common prefix
  exprt and_expr1=conjunction(n_op1);
  exprt and_expr2=conjunction(n_op2);

  g1=conjunction(op1);

  exprt tmp(and_expr2);
  tmp.make_not();

  if(tmp!=and_expr1)
  {
    if(and_expr1.is_true() || and_expr2.is_true())
    {
    }
    else
      // TODO: make simplify more capable and apply here
      g1.add(or_exprt(and_expr1, and_expr2));
  }

  return g1;
}

#if 0
/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (std::ostream &out, const guardt &g)
{
  forall_expr_list(it, g.guard_list)
    out << "*** " << it->pretty() << std::endl;
  return out;
}

/*******************************************************************\

Function: guardt::is_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool guardt::is_false() const
{
  forall_guard(it, guard_list)
    if(it->is_false())
      return true;

  return false;
}

/*******************************************************************\

Function: guardt::make_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guardt::make_false()
{
  guard_list.clear();
  guard_list.push_back(exprt());
  guard_list.back()=false_exprt();
}
#endif
