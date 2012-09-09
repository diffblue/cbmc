/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <assert.h>

#include <expr_util.h>
#include <std_expr.h>
#include <i2string.h>
#endif

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_start_thread(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  
  target.location(state.guard, state.source);

  #if 0  
  if(instruction.targets.size()<2)
    throw "start_thread with less than two targets";
    
  goto_programt::const_targett goto_target=
    instruction.targets.front();
    
  goto_programt::const_targett new_state_pc, state_pc;
  
  if(forward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  state.source.pc=state_pc;
  
  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[new_state_pc];

  goto_state_list.push_back(statet::goto_statet(state));
  statet::goto_statet &new_state=goto_state_list.back();
  
  #endif
}
