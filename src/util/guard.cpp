/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "std_expr.h"
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
  else if(is_true())
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

  exprt::operandst &op1=g1.operands();
  const exprt::operandst &op2=g2.operands();

  exprt::operandst::const_iterator it2=op2.begin();
  
  while(!op1.empty() &&
        it2!=op2.end() &&
        op1.front()==*it2)
  {
    op1.erase(op1.begin());
    it2++;
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

    return g1;
  }

  // find common prefix  
  exprt::operandst &op1=g1.operands();
  const exprt::operandst &op2=g2.operands();

  exprt::operandst::iterator it1=op1.begin();
  exprt::operandst::const_iterator it2=op2.begin();
  
  while(it1!=op1.end())
  {
    if(it2==op2.end())
      break;
      
    if(*it1!=*it2)
      break;

    it1++;
    it2++;
  }
  
  if(it2==op2.end()) return g1;

  // end of common prefix
  exprt::operandst n_op1(it1, op1.end());
  exprt::operandst n_op2(it2, op2.end());
  exprt and_expr1=conjunction(n_op1);
  exprt and_expr2=conjunction(n_op2);
  
  op1.erase(it1, op1.end());
  g1=conjunction(op1);
  
  exprt tmp(and_expr2);
  tmp.make_not();
  
  if(tmp!=and_expr1)
  {
    if(and_expr1.is_true() || and_expr2.is_true())
    {
    }
    else
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

