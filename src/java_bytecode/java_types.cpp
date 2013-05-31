/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/std_types.h>
#include <util/ieee_float.h>

#include "java_types.h"

/*******************************************************************\

Function: java_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_int_type()
{
  return signedbv_typet(32);
}

/*******************************************************************\

Function: java_long_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_long_type()
{
  return signedbv_typet(64);
}

/*******************************************************************\

Function: java_short_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_short_type()
{
  return signedbv_typet(16);
}

/*******************************************************************\

Function: java_byte_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_byte_type()
{
  return signedbv_typet(8);
}

/*******************************************************************\

Function: java_char_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_char_type()
{
  return unsignedbv_typet(16);
}

/*******************************************************************\

Function: java_float_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_float_type()
{
  return ieee_float_spect::single_precision().to_type();
}

/*******************************************************************\

Function: java_double_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_double_type()
{
  return ieee_float_spect::double_precision().to_type();
}

/*******************************************************************\

Function: java_boolean_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_boolean_type()
{
  return bool_typet();
}

/*******************************************************************\

Function: java_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_reference_type()
{
  return reference_typet();
}

/*******************************************************************\

Function: java_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_type(char t)
{
  switch(t)
  {
  case 'i': return java_int_type();
  case 'l': return java_long_type();
  case 's': return java_short_type();
  case 'b': return java_byte_type();
  case 'c': return java_char_type();
  case 'f': return java_float_type();
  case 'd': return java_double_type();
  case 'z': return java_boolean_type();
  case 'a': return java_reference_type();
  default: assert(false);
  }
}
