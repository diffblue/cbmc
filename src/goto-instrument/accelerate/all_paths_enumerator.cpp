/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "all_paths_enumerator.h"

bool all_paths_enumeratort::next(patht &path)
{
  if(last_path.empty())
  {
    // This is the first time we've been called -- build an initial
    // path.
    last_path.push_back(path_nodet(loop_header));

    // This shouldn't be able to fail.
    complete_path(last_path, 0);

    if(is_looping(last_path))
    {
      // If this was a loop path, we're good.  If it wasn't,
      // we'll keep enumerating paths until we hit a looping one.
      // This case is exactly the same as if someone just called
      // next() on us.
      path.clear();
      path.insert(path.begin(), last_path.begin(), last_path.end());
      return true;
    }
  }

  do
  {
#ifdef DEBUG
    std::cout << "Enumerating next path...\n";
#endif

    int decision=backtrack(last_path);
    complete_path(last_path, decision);

    if(is_looping(last_path))
    {
      path.clear();
      path.insert(path.begin(), last_path.begin(), last_path.end());
      return true;
    }
  }
  while(!last_path.empty());

  // We've enumerated all the paths.
  return false;
}

int all_paths_enumeratort::backtrack(patht &path)
{
  // If we have a path of length 1 or 0, we can't backtrack any further.
  // That means we're done enumerating paths!
  if(path.size()<2)
  {
    path.clear();
    return 0;
  }

  goto_programt::targett node_loc=path.back().loc;
  path.pop_back();

  goto_programt::targett parent_loc=path.back().loc;
  const auto succs=goto_program.get_successors(parent_loc);

  unsigned int ret=0;

  for(const auto &succ : succs)
  {
    if(succ==node_loc)
      break;

    ret++;
  }

  if((ret+1)<succs.size())
  {
    // We can take the next branch here...

#ifdef DEBUG
    std::cout << "Backtracked to a path of size " << path.size() << '\n';
#endif

    return ret+1;
  }

  // Recurse.
  return backtrack(path);
}

void all_paths_enumeratort::complete_path(patht &path, int succ)
{
  if(path.empty())
    return;

  goto_programt::targett node_loc=path.back().loc;
  extend_path(path, node_loc, succ);

  goto_programt::targett end=path.back().loc;

  if(end == loop_header || !loop.contains(end))
    return;

  complete_path(path, 0);
}

void all_paths_enumeratort::extend_path(
  patht &path,
  goto_programt::targett t,
  int succ)
{
  goto_programt::targett next;
  exprt guard=true_exprt();

  for(const auto &s : goto_program.get_successors(t))
  {
    if(succ==0)
    {
      next=s;
      break;
    }

    succ--;
  }

  if(t->is_goto())
  {
    guard = not_exprt(t->condition());

    for(goto_programt::targetst::iterator it=t->targets.begin();
        it != t->targets.end();
        ++it)
    {
      if(next == *it)
      {
        guard = t->condition();
        break;
      }
    }
  }

  path.push_back(path_nodet(next, guard));
}

bool all_paths_enumeratort::is_looping(patht &path)
{
  return path.size()>1 && path.back().loc==loop_header;
}
