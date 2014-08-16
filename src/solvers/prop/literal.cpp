/*******************************************************************\

Module: Literals

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "literal.h"

/*******************************************************************\

Function: cover_goalst::~cover_goalst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream & operator << (std::ostream &out, literalt l)
{
  return out << (l.sign()?"-":"") << l.var_no();
}

