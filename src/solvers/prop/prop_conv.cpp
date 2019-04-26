/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop_conv.h"

#include "literal_expr.h"

#include <util/std_expr.h>

#include <algorithm>

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
