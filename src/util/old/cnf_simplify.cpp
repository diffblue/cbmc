/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "cnf_simplify.h"
#include "expr.h"

void cnf_propagate_not(exprt &expr);
void cnf_join_binary(exprt &expr);
void propagate_not(exprt &expr);

/*******************************************************************\

Function: cnf_simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnf_simplify(exprt &expr)
{
  cnf_propagate_not(expr);
  cnf_join_binary(expr);
}

#if 0
/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnf_join_binary(exprt &expr)
{
  Forall_operands(it, expr)
    cnf_join_binary(*it);

  if(expr.id()==ID_and || expr.id()==ID_or || expr.id()==ID_xor ||
     expr.id()==ID_bitand || expr.id()==ID_bitor || expr.id()==ID_bitxor)
  {
    exprt tmp;

    if(expr.operands().size()==1)
    {
      tmp.swap(expr.op0());
      expr.swap(tmp);
    }
    else
    {
      unsigned count=0;

      forall_operands(it, expr)
      {
        if(it->id()==expr.id())
          count+=it->operands().size();
        else
          count++;
      }

      tmp.operands().reserve(count);

      Forall_operands(it, expr)
      {
        if(it->id()==expr.id())
        {
          Forall_operands(it2, *it)
            tmp.move_to_operands(*it2);
        }
        else
          tmp.move_to_operands(*it);
      }

      expr.operands().swap(tmp.operands());
    }
  }
}
#endif

/*******************************************************************\

Function: cnf_join_binary_collect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnf_join_binary_collect(exprt &expr, exprt::operandst &list)
{
  Forall_operands(it, expr)
  {
    if(it->id()==expr.id() && it->type()==expr.type())
      cnf_join_binary_collect(*it, list);
    else
    {
      list.resize(list.size()+1);
      list.back().swap(*it);
    }
  }
}

/*******************************************************************\

Function: cnf_join_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnf_join_binary(exprt &expr)
{
  if(expr.id()==ID_and || expr.id()==ID_or || expr.id()==ID_xor ||
     expr.id()==ID_bitand || expr.id()==ID_bitor || expr.id()==ID_bitxor)
  {
    exprt::operandst list;

    cnf_join_binary_collect(expr, list);

    if(list.size()==1)
      expr.swap(list.front());
    else
      expr.operands().swap(list);
  }

  Forall_operands(it, expr)
    cnf_join_binary(*it);
}

/*******************************************************************\

Function: cnf_propagate_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cnf_propagate_not(exprt &expr)
{
  if(expr.id()==ID_not)
  {
    if(expr.operands().size()==1)
    {
      exprt tmp;

      tmp.swap(expr.op0());
      propagate_not(tmp);
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_nor)
  {
    expr.id(ID_or);
    propagate_not(expr);
  }
  else if(expr.id()==ID_nand)
  {
    expr.id(ID_and);
    propagate_not(expr);
  }
  else if(expr.id()==ID_implies)
  {
    if(expr.operands().size()==2)
    {
      expr.id(ID_or);
      propagate_not(expr.op0());
    }
  }

  Forall_operands(it, expr)
    cnf_propagate_not(*it);  
}

/*******************************************************************\

Function: propagate_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void propagate_not(exprt &expr)
{
  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(expr.id()==ID_and)
      expr.id(ID_or);
    else // or
      expr.id(ID_and);

    Forall_operands(it, expr)
      propagate_not(*it);
  }
  else if(expr.id()==ID_nor)
    expr.id(ID_or);
  else if(expr.id()==ID_nand)
    expr.id(ID_and);
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
  }
  else if(expr.id()==ID_equal)
    expr.id(ID_notequal);
  else if(expr.id()==ID_notequal)
    expr.id(ID_equal);
  else
  {
    exprt tmp;
    expr.swap(tmp);
    expr.id(ID_not);
    expr.type()=tmp.type();
    expr.move_to_operands(tmp);
  }
}
