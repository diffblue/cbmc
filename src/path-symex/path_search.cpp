/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <path-symex/path_symex.h>

#include "path_search.h"

/*******************************************************************\

Function: path_searcht::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_searcht::operator()(
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions)
{
  namespacet ns(symbol_table);
  locst locs(ns);
  var_mapt var_map(ns);
  
  locs.build(goto_functions);
  
  queue.push_back(initial_state(var_map, locs));
  
  while(!queue.empty())
  {
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();
    
    if(!state->is_executable())
    {
      queue.erase(state);
      continue;
    }
    
    status() << "Queue " << queue.size()
             << " thread " << state->get_current_thread()
             << "/" << state->threads.size()
             << " PC " << state->pc() << messaget::eom;

    // an error, possibly?
    if(state->get_instruction()->is_assert())
      if(check_assertion(*state, ns))
        return true; // property fails
    
    // execute
    path_symex(*state, queue, ns);
  }

  return false; // property holds
}

/*******************************************************************\

Function: path_searcht::pick_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_searcht::queuet::iterator path_searcht::pick_state()
{
  // Picking the first one is a DFS.
  return queue.begin();
}

/*******************************************************************\

Function: path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_searcht::check_assertion(
  const statet &state,
  const namespacet &ns)
{
  return false; // no error
}
