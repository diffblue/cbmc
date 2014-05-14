#ifndef PATH_ENUMERATOR_H
#define PATH_ENUMERATOR_H

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>

#include "path.h"

class path_enumeratort {
 public:
  virtual ~path_enumeratort() {
  }

  virtual bool next(patht &path) = 0;
};

#endif // PATH_ENUMERATOR_H
