#ifndef PATH_ACCELERATOR_H
#define PATH_ACCELERATOR_H

#include "path.h"

#include <set>

#include <util/std_expr.h>

#include <analyses/natural_loops.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

class path_acceleratort {
 public:
  path_acceleratort(goto_programt &pure,
               goto_programt &overflow,
               std::set<exprt> &changed,
               std::set<exprt> &dirty) :
    pure_accelerator(pure),
    overflow_path(overflow),
    changed_vars(changed),
    dirty_vars(dirty)
  {
  }

  path_acceleratort() { }

  goto_programt pure_accelerator;
  goto_programt overflow_path;
  std::set<exprt> changed_vars;
  std::set<exprt> dirty_vars;
};

#endif // PATH_ACCELERATOR_H
