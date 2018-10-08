/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_C_TYPES_H
#define CPROVER_UTIL_C_TYPES_H

#include "std_types.h"

bitvector_typet index_type();
bitvector_typet enum_constant_type();
signedbv_typet signed_int_type();
unsignedbv_typet unsigned_int_type();
signedbv_typet signed_long_int_type();
signedbv_typet signed_short_int_type();
unsignedbv_typet unsigned_short_int_type();
signedbv_typet signed_long_long_int_type();
unsignedbv_typet unsigned_long_int_type();
unsignedbv_typet unsigned_long_long_int_type();
typet c_bool_type();
bitvector_typet char_type();
unsignedbv_typet unsigned_char_type();
signedbv_typet signed_char_type();
bitvector_typet wchar_t_type();
unsignedbv_typet char16_t_type();
unsignedbv_typet char32_t_type();
floatbv_typet float_type();
floatbv_typet double_type();
floatbv_typet long_double_type();
unsignedbv_typet size_type();
signedbv_typet signed_size_type();
signedbv_typet pointer_diff_type();
pointer_typet pointer_type(const typet &);
typet void_type();

// This is for Java and C++
reference_typet reference_type(const typet &);

// Turns an ID_C_c_type into a string, e.g.,
// ID_signed_int gets "signed int".
std::string c_type_as_string(const irep_idt &);

#endif // CPROVER_UTIL_C_TYPES_H
