/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ARITH_TOOLS_H
#define CPROVER_ARITH_TOOLS_H

#include "mp_arith.h"

class exprt;
class typet;

bool to_integer(const exprt &expr, mp_integer &int_value);
exprt from_integer(const mp_integer &int_value, const typet &type);

// ceil(log2(size))
mp_integer address_bits(const mp_integer &size);

mp_integer power(const mp_integer &base, const mp_integer &exponent);

void mp_min(mp_integer &a, const mp_integer &b);
void mp_max(mp_integer &a, const mp_integer &b);

#endif
