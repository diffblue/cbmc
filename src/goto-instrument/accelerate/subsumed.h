/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_SUBSUMED_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_SUBSUMED_H

#include "path.h"

#include <list>

class subsumed_patht
{
public:
  explicit subsumed_patht(patht &_subsumed)
  {
    patht::iterator it = subsumed.begin();
    subsumed.insert(it, _subsumed.begin(), _subsumed.end());
  }

  patht subsumed;
  patht accelerator;
  patht residue;
};

typedef std::list<subsumed_patht> subsumed_pathst;

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_SUBSUMED_H
