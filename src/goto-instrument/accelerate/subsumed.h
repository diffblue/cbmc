#ifndef SUBSUMED_H
#define SUBSUMED_H

#include "path.h"

#include <list>

class subsumed_patht {
 public:
  subsumed_patht(patht &_subsumed) {
    patht::iterator it = subsumed.begin();
    subsumed.insert(it, _subsumed.begin(), _subsumed.end());
  }

  patht subsumed;
  patht accelerator;
  patht residue;
};

typedef list<subsumed_patht> subsumed_pathst;

#endif // SUBSUMED_H
