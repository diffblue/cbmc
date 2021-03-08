/*******************************************************************\

Module: Pre-defined bitvector types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pre-defined bitvector types

#include "bitvector_types.h"

#include "arith_tools.h"
#include "bv_arithmetic.h"
#include "std_expr.h"
#include "string2int.h"

std::size_t fixedbv_typet::get_integer_bits() const
{
  const irep_idt integer_bits = get(ID_integer_bits);
  DATA_INVARIANT(!integer_bits.empty(), "integer bits should be set");
  return unsafe_string2unsigned(id2string(integer_bits));
}

std::size_t floatbv_typet::get_f() const
{
  const irep_idt &f = get(ID_f);
  DATA_INVARIANT(!f.empty(), "the mantissa should be set");
  return unsafe_string2unsigned(id2string(f));
}

mp_integer integer_bitvector_typet::smallest() const
{
  return bv_spect(*this).min_value();
}

mp_integer integer_bitvector_typet::largest() const
{
  return bv_spect(*this).max_value();
}

constant_exprt integer_bitvector_typet::zero_expr() const
{
  return from_integer(0, *this);
}

constant_exprt integer_bitvector_typet::smallest_expr() const
{
  return from_integer(smallest(), *this);
}

constant_exprt integer_bitvector_typet::largest_expr() const
{
  return from_integer(largest(), *this);
}
