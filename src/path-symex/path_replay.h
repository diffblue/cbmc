/*******************************************************************\

Module: Dense Data Structure for Path Replay

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dense Data Structure for Path Replay

#ifndef CPROVER_PATH_SYMEX_PATH_REPLAY_H
#define CPROVER_PATH_SYMEX_PATH_REPLAY_H

#include "path_symex_state.h"

class path_replayt
{
public:
  path_replayt()
  {
  }

  explicit path_replayt(const path_symex_statet &src)
  {
    get_branches(src.history);
  }

  void replay(path_symex_statet &);

protected:
  // TODO: consider something even denser, say something like a bitset
  using branchest = std::vector<bool>;
  branchest branches;

  void get_branches(const path_symex_step_reft history);
};

void path_replay(path_symex_step_reft history);

#endif // CPROVER_PATH_SYMEX_PATH_REPLAY_H
