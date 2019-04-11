/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop_conv.h"

#include "literal_expr.h"

#include <util/std_expr.h>

#include <algorithm>

exprt prop_convt::handle(const exprt &expr)
{
  // We can only improve Booleans.
  if(expr.type().id() != ID_bool)
    return expr;

  // We convert to a literal to obtain a 'small' handle
  literalt l = convert(expr);

  // The literal may be a constant as a result of non-trivial
  // propagation. We return constants as such.
  if(l.is_true())
    return true_exprt();
  else if(l.is_false())
    return false_exprt();

  // freeze to enable incremental use
  set_frozen(l);

  return literal_exprt(l);
}

/// determine whether a variable is in the final conflict
bool prop_convt::is_in_conflict(literalt) const
{
  UNREACHABLE;
  return false;
}

void prop_convt::set_assumptions(const bvt &)
{
  UNREACHABLE;
}

void prop_convt::set_frozen(const literalt)
{
  UNREACHABLE;
}

void prop_convt::set_frozen(const bvt &bv)
{
  for(const auto &bit : bv)
    if(!bit.is_constant())
      set_frozen(bit);
}
