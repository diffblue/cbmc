/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_GCC_TYPES_H
#define CPROVER_ANSI_C_GCC_TYPES_H

#include <util/std_types.h>

// These are gcc-specific; most are not implemented by clang
// https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html

floatbv_typet gcc_float16_type();
floatbv_typet gcc_float32_type();
floatbv_typet gcc_float32x_type();
floatbv_typet gcc_float64_type();
floatbv_typet gcc_float64x_type();
floatbv_typet gcc_float128_type();
floatbv_typet gcc_float128x_type();
unsignedbv_typet gcc_unsigned_int128_type();
signedbv_typet gcc_signed_int128_type();

#endif // CPROVER_ANSI_C_GCC_TYPES_H
