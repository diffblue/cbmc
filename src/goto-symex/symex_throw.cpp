/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_throw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_throw(statet &state)
{
  #if 0  
  const goto_programt::instructiont &instruction=*state.source.pc;

  // get the list of exceptions thrown
  const irept::subt &exceptions_thrown=
    instruction.code.find(ID_exception_list).get_sub();

  // go through the call stack, beginning with the top

  for(goto_symex_statet::call_stackt::const_reverse_iterator
      s_it=state.call_stack.rbegin();
      s_it!=state.call_stack.rend();
      s_it++)
  {
    const goto_symex_statet::framet &frame=*s_it;
    
    if(frame.catch_map.empty()) continue;
  
    for(irept::subt::const_iterator 
        e_it=exceptions_thrown.begin();
        e_it!=exceptions_thrown.end();
        e_it++)
    {
      goto_symex_statet::framet::catch_mapt::const_iterator
        c_it=frame.catch_map.find(e_it->id());
        
      if(c_it!=frame.catch_map.end())
      {
        // found -- these are always forward gotos
      }
    }
  }
  #endif
  
  // An un-caught exception. Behaves like assume(0);
  state.guard.add(false_exprt());
  exprt tmp=state.guard.as_expr();
  target.assumption(state.guard, tmp, state.source);
}
