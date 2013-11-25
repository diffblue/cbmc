/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "substitute.h"

/*******************************************************************\

Function: substitute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void substitute(
  std::string &dest,
  const std::string &what,
  const std::string &by)
{
  assert(!what.empty());
  
  while(true)
  {
    std::string::size_type pos=dest.find(what);
    
    if(pos==std::string::npos)
      return; // done

    dest.replace(dest.begin()+pos,
                 dest.begin()+pos+what.size(),
                 by);
  }
}
