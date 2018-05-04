/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "gcc_types.h"

#include <util/config.h>
#include <util/c_types.h>

bitvector_typet gcc_float16_type()
{
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(16);
    result.set_integer_bits(16/2);
    result.set(ID_C_c_type, ID_gcc_float16);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::half_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float16);
    return result;
  }
}

bitvector_typet gcc_float32_type()
{
  // not same as float!

  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(config.ansi_c.single_width);
    result.set_integer_bits(config.ansi_c.single_width/2);
    result.set(ID_C_c_type, ID_gcc_float32);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::single_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float32);
    return result;
  }
}

bitvector_typet gcc_float32x_type()
{
  // not same as float!

  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(config.ansi_c.single_width);
    result.set_integer_bits(config.ansi_c.single_width/2);
    result.set(ID_C_c_type, ID_gcc_float32x);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::single_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float32x);
    return result;
  }
}

bitvector_typet gcc_float64_type()
{
  // not same as double!
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(config.ansi_c.double_width);
    result.set_integer_bits(config.ansi_c.double_width/2);
    result.set(ID_C_c_type, ID_gcc_float64);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::double_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float64);
    return result;
  }
}

bitvector_typet gcc_float64x_type()
{
  // not same as double!
  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(config.ansi_c.double_width);
    result.set_integer_bits(config.ansi_c.double_width/2);
    result.set(ID_C_c_type, ID_gcc_float64x);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::double_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float64x);
    return result;
  }
}

bitvector_typet gcc_float128_type()
{
  // not same as long double!

  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(128);
    result.set_integer_bits(128/2);
    result.set(ID_C_c_type, ID_gcc_float128);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::quadruple_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float128);
    return result;
  }
}

bitvector_typet gcc_float128x_type()
{
  // not same as long double!

  if(config.ansi_c.use_fixed_for_float)
  {
    fixedbv_typet result;
    result.set_width(128);
    result.set_integer_bits(128/2);
    result.set(ID_C_c_type, ID_gcc_float128x);
    return result;
  }
  else
  {
    floatbv_typet result=
      ieee_float_spect::quadruple_precision().to_type();
    result.set(ID_C_c_type, ID_gcc_float128x);
    return result;
  }
}

unsignedbv_typet gcc_unsigned_int128_type()
{
  unsignedbv_typet result(128);
  result.set(ID_C_c_type, ID_unsigned_int128);
  return result;
}

signedbv_typet gcc_signed_int128_type()
{
  signedbv_typet result(128);
  result.set(ID_C_c_type, ID_signed_int128);
  return result;
}
