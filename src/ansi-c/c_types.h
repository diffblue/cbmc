/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_TYPES_H
#define CPROVER_C_TYPES_H

#include <expr.h>

typet index_type();
typet enum_type();
typet int_type(); // will go away
typet uint_type(); // will go away
typet signed_int_type();
typet unsigned_int_type();
typet long_int_type(); // will go away
typet signed_long_int_type();
typet signed_short_int_type();
typet unsigned_short_int_type();
typet long_long_int_type(); // will go away
typet signed_long_long_int_type();
typet long_uint_type(); // will go away
typet long_long_uint_type(); // will go away
typet unsigned_long_int_type();
typet unsigned_long_long_int_type();
typet c_bool_type();
typet char_type();
typet unsigned_char_type();
typet signed_char_type();
typet wchar_t_type();
typet char16_t_type();
typet char32_t_type();
typet float_type();
typet double_type();
typet long_double_type();
typet gcc_float128_type();
typet gcc_unsigned_int128_type();
typet gcc_signed_int128_type();
typet size_type();
typet signed_size_type();
typet pointer_diff_type();

#endif
