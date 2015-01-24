/*******************************************************************\

Module: ILP construction for cycles affecting user-assertions 
        and resolution

Author: Vincent Nimal

\*******************************************************************/

#include "fence_assert.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fence_assert_insertert::find_assert(
  const event_grapht::critical_cyclet& cycle) const 
{
  /* TODO */
  return true;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_assert_insertert::process_cycles_selection()
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    if( find_assert(*C_j) )
      selected_cycles.insert(C_j->id);
  }
}
