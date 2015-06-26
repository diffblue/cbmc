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
  else if(type.id()==ID_c_bool)
    return IS_C_BOOL;
  else if(type.id()==ID_c_enum ||
          type.id()==ID_c_enum_tag ||
          type.id()==ID_incomplete_c_enum)
    return IS_C_ENUM;
  else if(type.id()==ID_floatbv)
    return IS_FLOAT;
  else if(type.id()==ID_fixedbv)
    return IS_FIXED;
  else if(type.id()==ID_bv)
    return IS_BV;
  else if(type.id()==ID_verilog_signedbv)
    return IS_VERILOG_SIGNED;
  else if(type.id()==ID_verilog_unsignedbv)
    return IS_VERILOG_UNSIGNED;
  else if(type.id()==ID_range)
    return IS_RANGE;
  else if(type.id()==ID_c_bit_field)
    return IS_C_BIT_FIELD;

  return IS_UNKNOWN;
}
