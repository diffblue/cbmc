/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_catch(statet &state)
{
  // there are two variants: 'push' and 'pop'
 
  #if 0 
  const goto_programt::instructiont &instruction=*state.source.pc;

  if(instruction.targets.empty()) // pop
  {
    if(state.call_stack.empty())
      throw "catch-pop on empty call stack";

    if(state.top().catch_map.empty())
      throw "catch-pop on function frame";

    // pop the stack frame
    state.call_stack.pop_back();
  }
  else // push
  {
    state.catch_stack.push_back(goto_symex_statet::catch_framet());
    goto_symex_statet::catch_framet &frame=state.catch_stack.back();
    
    // copy targets
    const irept::subt &exception_list=
      instruction.code.find(ID_exception_list).get_sub();
    
    assert(exception_list.size()==instruction.targets.size());
    
    unsigned i=0;
    
    for(goto_programt::targetst::const_iterator
        it=instruction.targets.begin();
        it!=instruction.targets.end();
        it++, i++)
      frame.target_map[exception_list[i].id()]=*it;
  }
  #endif
}
