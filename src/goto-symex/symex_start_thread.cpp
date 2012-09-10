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

  #if 0
  const goto_programt::instructiont &instruction=*state.source.pc;
  
  if(instruction.targets.size()!=1)
    throw "start_thread expects one target";
    
  goto_programt::const_targett thread_target=
    instruction.targets.front();

  // put into thread-queue
  state.threads.push_back(statet::threadt());
  statet::threadt &new_thread=state.threads.back();
  new_thread.source.pc=thread_target;
  new_thread.source.thread_nr=++state.thread_count;
  new_thread.guard=state.guard;
  new_thread.function_identifier=state.top().function_identifier;
  new_thread.calling_location=state.top().calling_location;
  new_thread.end_of_function=state.top().end_of_function;                    
  #endif
}

