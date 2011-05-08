/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include "simplify_utils.h"

/*******************************************************************\

Function: simplify_exprt::sort_operands

  Inputs: operand list

 Outputs: modifies operand list
          returns true iff nothing was changed

 Purpose: sort operands of an expression according to ordering
          defined by operator<

\*******************************************************************/

bool sort_operands(exprt::operandst &operands)
{
  bool do_sort=false;

  forall_expr(it, operands)
  {
    exprt::operandst::const_iterator next_it=it;
    next_it++;

    if(next_it!=operands.end() && *next_it < *it)
    {
      do_sort=true;
      break;
    }
  }

  if(!do_sort) return true;

  std::sort(operands.begin(), operands.end());

  return false;
}
