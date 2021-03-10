/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_UTIL_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_UTIL_H

#include <util/bitvector_types.h>

signedbv_typet signed_poly_type();
unsignedbv_typet unsigned_poly_type();

bool is_bitvector(const typet &t);
typet join_types(const typet &t1, const typet &t2);

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_UTIL_H
