/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "gcc_types.h"

#include <util/config.h>
#include <util/c_types.h>

floatbv_typet gcc_float16_type()
{
  floatbv_typet result=
    ieee_float_spect::half_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float16);
  return result;
}

floatbv_typet gcc_float32_type()
{
  // not same as float!
  floatbv_typet result=
    ieee_float_spect::single_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float32);
  return result;
}

floatbv_typet gcc_float32x_type()
{
  // not same as float!
  floatbv_typet result=
    ieee_float_spect::single_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float32x);
  return result;
}

floatbv_typet gcc_float64_type()
{
  // not same as double!
  floatbv_typet result=
    ieee_float_spect::double_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float64);
  return result;
}

floatbv_typet gcc_float64x_type()
{
  // not same as double!
  floatbv_typet result=
    ieee_float_spect::double_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float64x);
  return result;
}

floatbv_typet gcc_float128_type()
{
  // not same as long double!
  floatbv_typet result=
    ieee_float_spect::quadruple_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float128);
  return result;
}

floatbv_typet gcc_float128x_type()
{
  // not same as long double!
  floatbv_typet result=
    ieee_float_spect::quadruple_precision().to_type();
  result.set(ID_C_c_type, ID_gcc_float128x);
  return result;
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
