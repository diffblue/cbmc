/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "merge_irep.h"

/*******************************************************************\

Function: merge_irept::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void merge_irept::operator()(irept &irep)
{
  irep_storet::const_iterator entry=irep_store.find(irep);
  if(entry!=irep_store.end())
  {
    irep=*entry;
    return;
  }

  irept::subt &sub=irep.get_sub();
  Forall_irep(it, sub)
    operator()(*it); // recursive call

  irept::named_subt &named_sub=irep.get_named_sub();
  Forall_named_irep(it, named_sub)
    operator()(it->second); // recursive call

  irep=*irep_store.insert(irep).first;
}
