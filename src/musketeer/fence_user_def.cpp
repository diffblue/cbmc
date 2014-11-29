/*******************************************************************\

Module: ILP construction for cycles affecting user-assertions 
        and resolution

Author: Vincent Nimal

\*******************************************************************/

#include "fence_user_def.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fence_user_def_insertert::contains_user_def(
  const event_grapht::critical_cyclet& cycle) const 
{
  /* DEPRECATED: user-inserted fences now detected at cycle collection */
  #if 0
  /* if a fence already appears in the representation of the cycle, ok */
  for(event_grapht::critical_cyclet::const_iterator it=cycle.begin();
    it!=cycle.end(); ++it)
    if(egraph[*it].is_fence())
      return true;

  /* we collect the fences back in the graph; indeed, in the cycles we extract,
     it is possible that some lwfence have been ignored, as they had no effect
     (in the case of WR) */
  #endif  

  return cycle.has_user_defined_fence;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_user_def_insertert::process_cycles_selection()
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    if( contains_user_def(*C_j) )
      selected_cycles.insert(C_j->id);
  }
}
