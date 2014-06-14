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
  path_acceleratort(patht &_path,
               goto_programt &pure,
               goto_programt &overflow,
               std::set<exprt> &changed,
               std::set<exprt> &dirty) :
    path(_path),
    changed_vars(changed),
    dirty_vars(dirty)
  {
    pure_accelerator.copy_from(pure);
    overflow_path.copy_from(overflow);
  }

  path_acceleratort() { }

  path_acceleratort(const path_acceleratort &that) :
    path(that.path),
    changed_vars(that.changed_vars),
    dirty_vars(that.dirty_vars) 
  {
    pure_accelerator.copy_from(that.pure_accelerator);
    overflow_path.copy_from(that.overflow_path);
  }

  void clear() {
    path.clear();
    pure_accelerator.clear();
    overflow_path.clear();
    changed_vars.clear();
    dirty_vars.clear();
  }

  patht path;
  goto_programt pure_accelerator;
  goto_programt overflow_path;
  std::set<exprt> changed_vars;
  std::set<exprt> dirty_vars;
};

#endif // PATH_ACCELERATOR_H
