/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"

/*******************************************************************\

Function: disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt disjunction(const exprt::operandst &op)
{
  if(op.empty())
    return false_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    or_exprt result;
    result.operands()=op;
    return result;
  }
}

/*******************************************************************\

Function: conjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt conjunction(const exprt::operandst &op)
{
  if(op.empty())
    return true_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    and_exprt result;
    result.operands()=op;
    return result;
  }
}

