/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "replace_expr.h"

/*******************************************************************\

Function: replace_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_expr(const exprt &what, const exprt &by, exprt &dest)
{
  if(dest==what)
  {
    dest=by;
    return false;
  }

  bool result=true;

  Forall_operands(it, dest)
    result=replace_expr(what, by, *it) && result;

  return result;
}

/*******************************************************************\

Function: replace_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_expr(const replace_mapt &what, exprt &dest)
{
  {
    replace_mapt::const_iterator it=what.find(dest);

    if(it!=what.end())
    {
      dest=it->second;
      return false;
    }
  }

  bool result=true;

  Forall_operands(it, dest)
    result=replace_expr(what, *it) && result;

  return result;
}

