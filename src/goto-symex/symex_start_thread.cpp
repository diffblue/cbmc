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
  if(state.guard.is_false()) return;

  // record the location
  target.location(state.guard, state.source);

  const goto_programt::instructiont &instruction=*state.source.pc;
  
  if(instruction.targets.size()!=1)
    throw "start_thread expects one target";
    
  goto_programt::const_targett thread_target=
    instruction.targets.front();

  // put into thread vector
  unsigned t=state.threads.size();
  state.threads.push_back(statet::threadt());
  statet::threadt &new_thread=state.threads.back();
  new_thread.pc=thread_target;
  new_thread.guard=state.guard;
  new_thread.call_stack.push_back(state.top());
  new_thread.parent_thread=state.source.thread_nr;

  // create a copy of the local variables for the new thread
  statet::framet &frame=state.top();

  for(std::set<irep_idt>::const_iterator
      it=frame.local_variables.begin();
      it!=frame.local_variables.end();
      it++)
  {
    // get original name
    irep_idt original_name=state.get_original_name(*it);
  
    // get L0 name for current thread
    irep_idt l0_name=state.level0.name(original_name, t);
    
    // setup L1 name
    state.level1.rename(l0_name, 0);
    irep_idt l1_name=state.level1.current_name(l0_name);
    state.l1_history.insert(l1_name);
    
    // make copy
    typet type=ns.lookup(original_name).type;
    symbol_exprt lhs(l1_name, type);
    symbol_exprt rhs(*it, type);

    symex_assign_symbol(state, lhs, nil_exprt(), rhs, state.guard, HIDDEN);
  }
}

