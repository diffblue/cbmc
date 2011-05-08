/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_type.h"

/*******************************************************************\

Function: get_bvtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvtypet get_bvtype(const typet &type)
{
  if(type.id()==ID_signedbv)
    return IS_SIGNED;
  else if(type.id()==ID_unsignedbv)
    return IS_UNSIGNED;
  else if(type.id()==ID_c_enum ||
          type.id()==ID_incomplete_c_enum)
    return IS_C_ENUM;
  else if(type.id()==ID_floatbv)
    return IS_FLOAT;
  else if(type.id()==ID_fixedbv)
    return IS_FIXED;
  else if(type.id()==ID_bv)
    return IS_BV;
  else if(type.id()==ID_verilogbv)
    return IS_VERILOGBV;
  else if(type.id()==ID_range)
    return IS_RANGE;

  return IS_UNKNOWN;
}
