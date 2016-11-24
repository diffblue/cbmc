/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/config.h>

#include "c_types.h"

/*******************************************************************\

Function: index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet index_type()
{
  // same as signed size type
  return signed_size_type();
}

/*******************************************************************\

Function: enum_constant_type

  Inputs:

 Outputs:

 Purpose: return type of enum constants

\*******************************************************************/

typet enum_constant_type()
{
  // usually same as 'int',
  // but might be unsigned, or shorter than 'int'
  return signed_int_type();
}

/*******************************************************************\

Function: signed_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_int_type()
{
  typet result=signedbv_typet(config.ansi_c.int_width);  
  result.set(ID_C_c_type, ID_signed_int);
  return result;
}

/*******************************************************************\

Function: signed_short_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_short_int_type()
{
  typet result=signedbv_typet(config.ansi_c.short_int_width);
  result.set(ID_C_c_type, ID_signed_short_int);
  return result;
}

/*******************************************************************\

Function: unsigned_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet unsigned_int_type()
{
  typet result=unsignedbv_typet(config.ansi_c.int_width);  
  result.set(ID_C_c_type, ID_unsigned_int);
  return result;
}

/*******************************************************************\

Function: unsigned_short_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet unsigned_short_int_type()
{
  typet result=unsignedbv_typet(config.ansi_c.short_int_width);  
  result.set(ID_C_c_type, ID_unsigned_short_int);
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
  // The size type varies. This is unsigned int on some systems,
  // and unsigned long int on others,
  // and unsigned long long on say Windows 64.

  if(config.ansi_c.pointer_width==config.ansi_c.int_width)
    return unsigned_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_int_width)
    return unsigned_long_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_long_int_width)
    return unsigned_long_long_int_type();
  else
    assert(false); // aaah!
}

/*******************************************************************\

Function: signed_size_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_size_type()
{
  // we presume this is the same as pointer difference
  return pointer_diff_type();
}

/*******************************************************************\

Function: signed_long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_long_int_type()
{
  typet result=signedbv_typet(config.ansi_c.long_int_width);
  result.set(ID_C_c_type, ID_signed_long_int);
  return result;
}

/*******************************************************************\

Function: signed_long_long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_long_long_int_type()
{
  typet result=signedbv_typet(config.ansi_c.long_long_int_width);
  result.set(ID_C_c_type, ID_signed_long_long_int);
  return result;
}

/*******************************************************************\

Function: unsigned_long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet unsigned_long_int_type()
{
  typet result=unsignedbv_typet(config.ansi_c.long_int_width);  
  result.set(ID_C_c_type, ID_unsigned_long_int);
  return result;
}

/*******************************************************************\

Function: unsigned_long_long_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet unsigned_long_long_int_type()
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
  typet result=c_bool_typet(config.ansi_c.bool_width);
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

  // this can be signed or unsigned, depending on the architecture

  if(config.ansi_c.char_is_unsigned)
    result=unsignedbv_typet(config.ansi_c.char_width);
  else
    result=signedbv_typet(config.ansi_c.char_width);

  // There are 3 char types, i.e., this one is
  // different from either signed char or unsigned char!
    
  result.set(ID_C_c_type, ID_char);
    
  return result;
}

/*******************************************************************\

Function: unsigned_char_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet unsigned_char_type()
{
  typet result=unsignedbv_typet(config.ansi_c.char_width);

  result.set(ID_C_c_type, ID_unsigned_char);
  
  return result;
}

/*******************************************************************\

Function: signed_char_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet signed_char_type()
{
  typet result=signedbv_typet(config.ansi_c.char_width);

  result.set(ID_C_c_type, ID_signed_char);
  
  return result;
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

Function: char16_t_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet char16_t_type()
{
  typet result;

  // Types char16_t and char32_t denote distinct types with the same size,
  // signedness, and alignment as uint_least16_t and uint_least32_t,
  // respectively, in <stdint.h>, called the underlying types.
  result=unsignedbv_typet(16);

  result.set(ID_C_c_type, ID_char16_t);

  return result;
}

/*******************************************************************\

Function: char32_t_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet char32_t_type()
{
  typet result;
  
  // Types char16_t and char32_t denote distinct types with the same size,
  // signedness, and alignment as uint_least16_t and uint_least32_t,
  // respectively, in <stdint.h>, called the underlying types.
  result=unsignedbv_typet(32);

  result.set(ID_C_c_type, ID_char32_t);

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
    else if(config.ansi_c.long_double_width==80)
    {
      // x86 extended precision has 80 bits in total, and
      // deviating from IEEE, does not use a hidden bit.
      // We use the closest we have got, but the below isn't accurate.
      result=ieee_float_spect(63, 15).to_type();
    }
    else if(config.ansi_c.long_double_width==96)
    {
      result=ieee_float_spect(80, 15).to_type();
      // not quite right. The extra bits beyond 80 are usually padded.
    }
    else
      assert(false);
  }
  
  result.set(ID_C_c_type, ID_long_double);

  return result;
}

/*******************************************************************\

Function: gcc_float128_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet gcc_float128_type()
{
  typet result;
  
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet tmp;
    tmp.set_width(128);
    tmp.set_integer_bits(128/2);
    result=tmp;
  }
  else
  {
    result=ieee_float_spect::quadruple_precision().to_type();
  }

  // not same as long double!  
  result.set(ID_C_c_type, ID_gcc_float128);

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
  // The pointer-diff type varies. This is signed int on some systems,
  // and signed long int on others, and signed long long on say Windows.

  if(config.ansi_c.pointer_width==config.ansi_c.int_width)
    return signed_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_int_width)
    return signed_long_int_type();
  else if(config.ansi_c.pointer_width==config.ansi_c.long_long_int_width)
    return signed_long_long_int_type();
  else
    assert(false); // aaah!
}

/*******************************************************************\

Function: gcc_unsigned_int128_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet gcc_unsigned_int128_type()
{
  typet result=signedbv_typet(128);
  result.set(ID_C_c_type, ID_unsigned_int128);
  return result;
}

/*******************************************************************\

Function: gcc_signed_int128_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet gcc_signed_int128_type()
{
  typet result=signedbv_typet(128);
  result.set(ID_C_c_type, ID_signed_int128);
  return result;
}

/*******************************************************************\

Function: c_type_as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c_type_as_string(const irep_idt &c_type)
{
  if(c_type==ID_signed_int)
    return "signed int";
  else if(c_type==ID_signed_short_int)
    return "signed short int";
  else if(c_type==ID_unsigned_int)
    return "unsigned int";
  else if(c_type==ID_unsigned_short_int)
    return "unsigned short int";
  else if(c_type==ID_signed_long_int)
    return "signed long int";
  else if(c_type==ID_signed_long_long_int)
    return "signed long long int";
  else if(c_type==ID_unsigned_long_int)
    return "unsigned long int";
  else if(c_type==ID_unsigned_long_long_int)
    return "unsigned long long int";
  else if(c_type==ID_bool)
    return "_Bool";
  else if(c_type==ID_char)
    return "char";
  else if(c_type==ID_unsigned_char)
    return "unsigned char";
  else if(c_type==ID_signed_char)
    return "signed char";
  else if(c_type==ID_wchar_t)
    return "wchar_t";
  else if(c_type==ID_char16_t)
    return "char16_t";
  else if(c_type==ID_char32_t)
    return "char32_t";
  else if(c_type==ID_float)
    return "float";
  else if(c_type==ID_double)
    return "double";
  else if(c_type==ID_long_double)
    return "long double";
  else if(c_type==ID_gcc_float128)
    return "__float128";
  else if(c_type==ID_unsigned_int128)
    return "unsigned __int128";
  else if(c_type==ID_signed_int128)
    return "signed __int128";
  else
    return "";
}
