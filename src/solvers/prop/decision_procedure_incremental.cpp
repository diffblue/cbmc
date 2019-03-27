/*******************************************************************\

Module: Decision procedure with incremental solving

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "decision_procedure_incremental.h"

void decision_procedure_incrementalt::set_frozen(const bvt &bv)
{
  for(const auto &bit : bv)
    if(!bit.is_constant())
      set_frozen(bit);
}
