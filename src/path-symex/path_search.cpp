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
  
  queue.push_back(initial_state(var_map, locs));

  while(!queue.empty())
  {
    // pick a state from the queue
    queuet::iterator state=queue.begin();
    
    // execute
    if(execute(state, ns))
      return true; // property fails
  }

  return false; // property holds
}

/*******************************************************************\

Function: path_searcht::execute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_searcht::execute(
  queuet::iterator state,
  const namespacet &ns)
{
  if(!state->is_executable())
  {
    queue.erase(state);
    return false; // no error found
  }
  
  path_symex(*state, queue, ns);
  
  return false;
}

