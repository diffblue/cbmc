/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>

#include "c_types.h"
#include "config.h"

/*******************************************************************\

Function: index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet index_type()
{
  // same as signed size type
  return signedbv_typet(config.ansi_c.pointer_width);
}

/*******************************************************************\

Function: enum_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet enum_type()
{
  return signedbv_typet(config.ansi_c.int_width);  
}

/*******************************************************************\

Function: int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet int_type()
{
  typet result=signedbv_typet(config.ansi_c.int_width);  
  result.set(ID_C_c_type, ID_int);
  return result;
}

/*******************************************************************\

Function: uint_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet uint_type()
{
  typet result=unsignedbv_typet(config.ansi_c.int_width);  
  result.set(ID_C_c_type, ID_unsigned_int);
  return result;
}

/*******************************************************************\

Function: size_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet size_type()
{
  return unsignedbv_typet(config.ansi_c.pointer_width);  
}

/*******************************************************************\

Function: signed_size_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_size_type()
{
  return signedbv_typet(config.ansi_c.pointer_width);  
}

/*******************************************************************\

Function: long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet long_int_type()
{
  typet result=signedbv_typet(config.ansi_c.long_int_width);
  result.set(ID_C_c_type, ID_signed_long_int);
  return result;
}

/*******************************************************************\

Function: long_long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet long_long_int_type()
{
  typet result=signedbv_typet(config.ansi_c.long_long_int_width);
  result.set(ID_C_c_type, ID_signed_long_long_int);
  return result;
}

/*******************************************************************\

Function: long_uint_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet long_uint_type()
{
  typet result=unsignedbv_typet(config.ansi_c.long_int_width);  
  result.set(ID_C_c_type, ID_unsigned_long_int);
  return result;
}

/*******************************************************************\

Function: long_long_uint_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet long_long_uint_type()
{
  typet result=unsignedbv_typet(config.ansi_c.long_long_int_width);
  result.set(ID_C_c_type, ID_unsigned_long_long_int);
  return result;
}

/*******************************************************************\

Function: c_bool_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet c_bool_type()
{
  typet result=unsignedbv_typet(config.ansi_c.bool_width);
  result.set(ID_C_c_type, ID_bool);
  return result;
}

/*******************************************************************\

Function: char_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet char_type()
{
  typet result;

  if(config.ansi_c.char_is_unsigned)
    result=unsignedbv_typet(config.ansi_c.char_width);
  else
    result=signedbv_typet(config.ansi_c.char_width);
    
  result.set(ID_C_c_type, ID_char);
    
  return result;
}

/*******************************************************************\

Function: uchar_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet uchar_type()
{
  return unsignedbv_typet(config.ansi_c.char_width);
}

/*******************************************************************\

Function: wchar_t_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet wchar_t_type()
{
  typet result;
  
  if(config.ansi_c.wchar_t_is_unsigned)
    result=unsignedbv_typet(config.ansi_c.wchar_t_width);
  else
    result=signedbv_typet(config.ansi_c.wchar_t_width);

  result.set(ID_C_c_type, ID_wchar_t);
  return result;
}

/*******************************************************************\

Function: float_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet float_type()
{
  typet result;
  
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet tmp;
    tmp.set_width(config.ansi_c.single_width);
    tmp.set_integer_bits(config.ansi_c.single_width/2);
    result=tmp;
  }
  else
    result=ieee_float_spect::single_precision().to_type();

  result.set(ID_C_c_type, ID_float);
  return result;
}

/*******************************************************************\

Function: double_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet double_type()
{
  typet result;
  
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet tmp;
    tmp.set_width(config.ansi_c.double_width);
    tmp.set_integer_bits(config.ansi_c.double_width/2);
    result=tmp;
  }
  else
    result=ieee_float_spect::double_precision().to_type();
  
  result.set(ID_C_c_type, ID_double);
  return result;
}

/*******************************************************************\

Function: long_double_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet long_double_type()
{
  typet result;
  
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet tmp;
    tmp.set_width(config.ansi_c.long_double_width);
    tmp.set_integer_bits(config.ansi_c.long_double_width/2);
    result=tmp;
  }
  else
  {
    if(config.ansi_c.long_double_width==128)
      result=ieee_float_spect::quadruple_precision().to_type();
    else if(config.ansi_c.long_double_width==64)
      result=ieee_float_spect::double_precision().to_type();
    else if(config.ansi_c.long_double_width==96)
      result=ieee_float_spect(80, 15).to_type();
      // not quite right. Intel's extended precision isn't IEEE.
    else
      assert(false);
  }
  
  result.set(ID_C_c_type, ID_long_double);
  return result;
}

/*******************************************************************\

Function: pointer_diff_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet pointer_diff_type()
{
  return signedbv_typet(config.ansi_c.pointer_width);
}

