/*******************************************************************\

Module: Dense Data Structure for Path Replay

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "path_replay.h"

/*******************************************************************\

Function: path_replayt::get_branches

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_branches(path_symex_step_reft history)
{
  // history trees are traversed effectively only backwards
  for(; !history.is_nil(); --history)
  {
  }
}
