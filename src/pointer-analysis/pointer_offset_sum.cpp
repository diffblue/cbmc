/*******************************************************************\

Module: Pointer Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "pointer_offset_sum.h"

/*******************************************************************\

Function: pointer_offset_sum

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt pointer_offset_sum(const exprt &a, const exprt &b)
{
  if(a.id()=="unknown")
    return a;
  else if(b.id()=="unknown")
    return b;
  else if(a.is_zero())
    return b;
  else if(b.is_zero())
    return a;

  exprt new_offset("+", a.type());
  new_offset.copy_to_operands(a, b);

  if(new_offset.op1().type()!=a.type())
    new_offset.op1().make_typecast(a.type());

  return new_offset;
}
