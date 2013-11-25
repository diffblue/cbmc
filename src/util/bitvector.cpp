/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include "bitvector.h"
#include "type.h"

/*******************************************************************\

Function: bv_sem

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_semt bv_sem(const typet &type)
{
  if(type.id()==ID_bv)
    return BV_NONE;
  else if(type.id()==ID_unsignedbv)
    return BV_UNSIGNED;
  else if(type.id()==ID_signedbv)
    return BV_SIGNED;

  return BV_UNKNOWN;
}

/*******************************************************************\

Function: bv_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned bv_width(const typet &type)
{
  return atoi(type.get(ID_width).c_str());
}


