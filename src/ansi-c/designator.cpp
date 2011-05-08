/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "designator.h"

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (
  std::ostream &out,
  const designatort &designator)
{
  for(unsigned i=0; i<designator.size(); i++)
  {
    if(i!=0) out << ", ";
    out << designator[i].type.id() << " "
        << designator[i].index << "/" << designator[i].size;
  }
  
  return out;
}
