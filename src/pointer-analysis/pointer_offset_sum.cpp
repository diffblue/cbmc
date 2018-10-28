/*******************************************************************\

Module: Pointer Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Analysis

#include "pointer_offset_sum.h"

#include <util/std_expr.h>

exprt pointer_offset_sum(const exprt &a, const exprt &b)
{
  if(a.id()==ID_unknown)
    return a;
  else if(b.id()==ID_unknown)
    return b;
  else if(a.is_zero())
    return b;
  else if(b.is_zero())
    return a;

  plus_exprt new_offset(a, b);

  if(b.type() != a.type())
    new_offset.op1().make_typecast(a.type());

  return std::move(new_offset);
}
