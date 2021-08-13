/*******************************************************************\

Module: API to expression classes for floating-point arithmetic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "floatbv_expr.h"

#include "arith_tools.h"
#include "bitvector_types.h"

constant_exprt floatbv_rounding_mode(unsigned rm)
{
  // The 32 bits are an arbitrary choice;
  // e.g., float_utilst consumes other widths as well.
  // The type is signed to match the signature of fesetround.
  return ::from_integer(rm, signedbv_typet(32));
}
