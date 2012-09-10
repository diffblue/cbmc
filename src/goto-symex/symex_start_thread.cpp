/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_start_thread(statet &state)
{
  // record the location
  target.location(state.guard, state.source);

  const goto_programt::instructiont &instruction=*state.source.pc;
  
  if(instruction.targets.size()!=1)
    throw "start_thread expects one target";
    
  goto_programt::const_targett thread_target=
    instruction.targets.front();

  // put into thread vector
  state.threads.push_back(statet::threadt());
  statet::threadt &new_thread=state.threads.back();
  new_thread.pc=thread_target;
  new_thread.guard=state.guard;
  new_thread.call_stack.push_back(state.top());
}

