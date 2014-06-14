#include <iostream>

#include "all_paths_enumerator.h"

//#define DEBUG

bool all_paths_enumeratort::next(patht &path) {
  if (last_path.empty()) {
    // This is the first time we've been called -- build an initial
    // path.
    last_path.push_back(loop_header);

    // This shouldn't be able to fail.
    complete_path(last_path, 0);

    if (is_looping(last_path)) {
      // If this was a loop path, we're good.  If it wasn't,
      // we'll keep enumerating paths until we hit a looping one.
      // This case is exactly the same as if someone just called
      // next() on us.
      path.clear();
      path.insert(path.begin(), last_path.begin(), last_path.end());
      return true;
    }
  }

  do {
#ifdef DEBUG
    std::cout << "Enumerating next path..." << std::endl;
#endif

    int decision = backtrack(last_path);
    complete_path(last_path, decision);

    if (is_looping(last_path)) {
      path.clear();
      path.insert(path.begin(), last_path.begin(), last_path.end());
      return true;
    }
  } while (!last_path.empty());

  // We've enumerated all the paths.
  return false;
}

int all_paths_enumeratort::backtrack(patht &path) {
  // If we have a path of length 1 or 0, we can't backtrack any further.
  // That means we're done enumerating paths!
  if (path.size() < 2) {
    path.clear();
    return 0;
  }

  path_nodet &node = path.back();
  path.pop_back();

  path_nodet &parent = path.back();
  goto_programt::targetst succs;
  goto_program.get_successors(parent.loc, succs);

  int ret = 0;

  for (goto_programt::targetst::iterator it = succs.begin();
       it != succs.end();
       ++it) {
    if (*it == node.loc) {
      break;
    }

    ret++;
  }

  if ((ret + 1) < succs.size()) {
    // We can take the next branch here...

#ifdef DEBUG
    std::cout << "Backtracked to a path of size " << path.size() << std::endl;
#endif

    return ret + 1;
  }

  // Recurse.
  return backtrack(path);
}

void all_paths_enumeratort::complete_path(patht &path, int succ) {
  if (path.empty()) {
    return;
  }

  path_nodet &node = path.back();
  extend_path(path, node.loc, succ);

  goto_programt::targett end = path.back().loc;

  if (end == loop_header || loop.find(end) == loop.end()) {
    return;
  }

  complete_path(path, 0);
}

void all_paths_enumeratort::extend_path(patht &path,
    goto_programt::targett t,
    int succ) {
  goto_programt::targett next;
  goto_programt::targetst succs;
  exprt guard = true_exprt();

  goto_program.get_successors(t, succs);

  for (goto_programt::targetst::iterator it = succs.begin();
       it != succs.end();
       ++it) {
    if (succ == 0) {
      next = *it;
      break;
    }

    succ--;
  }

  if (t->is_goto()) {
    guard = not_exprt(t->guard);

    for (goto_programt::targetst::iterator it = t->targets.begin();
         it != t->targets.end();
         ++it) {
      if (next == *it) {
        guard = t->guard;
        break;
      }
    }
  }

  path.push_back(path_nodet(next, guard));
}

bool all_paths_enumeratort::is_looping(patht &path) {
  return path.size() > 1 && path.back().loc == loop_header;
}
