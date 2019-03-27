/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "decision_procedure_incremental.h"
#include <algorithm>

/// determine whether a variable is in the final conflict
bool decision_procedure_incrementalt::is_in_conflict(literalt) const
{
  UNREACHABLE;
  return false;
}

void decision_procedure_incrementalt::set_assumptions(const bvt &)
{
  UNREACHABLE;
}

void decision_procedure_incrementalt::set_frozen(const literalt)
{
  UNREACHABLE;
}

void decision_procedure_incrementalt::set_frozen(const bvt &bv)
{
  for(const auto &bit : bv)
    if(!bit.is_constant())
      set_frozen(bit);
}
