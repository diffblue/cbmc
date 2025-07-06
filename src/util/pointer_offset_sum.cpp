/*******************************************************************\

Module: Pointer Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Analysis

#include "pointer_offset_sum.h"

#include "std_expr.h"

exprt pointer_offset_sum(const exprt &a, const exprt &b)
{
  if(a.id() == ID_unknown)
    return a;
  else if(b.id() == ID_unknown)
    return b;
  else if(a == 0)
    return b;
  else if(b == 0)
    return a;

  return plus_exprt(a, typecast_exprt::conditional_cast(b, a.type()));
}
