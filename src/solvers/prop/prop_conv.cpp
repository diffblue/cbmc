/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop_conv.h"

#include "literal_expr.h"

#include <algorithm>

exprt prop_convt::handle(const exprt &expr)
{
  return literal_exprt(convert(expr));
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
