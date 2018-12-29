/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv_type.h"

bvtypet get_bvtype(const typet &type)
{
  if(type.id()==ID_signedbv)
    return bvtypet::IS_SIGNED;
  else if(type.id()==ID_unsignedbv)
    return bvtypet::IS_UNSIGNED;
  else if(type.id()==ID_c_bool)
    return bvtypet::IS_C_BOOL;
  else if(type.id() == ID_c_enum || type.id() == ID_c_enum_tag)
    return bvtypet::IS_C_ENUM;
  else if(type.id()==ID_floatbv)
    return bvtypet::IS_FLOAT;
  else if(type.id()==ID_fixedbv)
    return bvtypet::IS_FIXED;
  else if(type.id()==ID_bv)
    return bvtypet::IS_BV;
  else if(type.id()==ID_verilog_signedbv)
    return bvtypet::IS_VERILOG_SIGNED;
  else if(type.id()==ID_verilog_unsignedbv)
    return bvtypet::IS_VERILOG_UNSIGNED;
  else if(type.id()==ID_range)
    return bvtypet::IS_RANGE;
  else if(type.id()==ID_c_bit_field)
    return bvtypet::IS_C_BIT_FIELD;

  return bvtypet::IS_UNKNOWN;
}
