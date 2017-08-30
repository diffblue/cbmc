/*******************************************************************\

Module: Dense Data Structure for Path Replay

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dense Data Structure for Path Replay

#include "path_replay.h"

void get_branches(path_symex_step_reft history)
{
  // history trees are traversed effectively only backwards
  for(; !history.is_nil(); --history)
  {
  }
}
