/*******************************************************************\

Module: Literals

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "literal.h"

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (std::ostream &out, literalt l)
{
  if(l.is_constant())
    return out << (l.is_true()?"true":"false");
  else
    return out << (l.sign()?"-":"") << l.var_no();
}
