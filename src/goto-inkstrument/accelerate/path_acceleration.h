/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ACCELERATION_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ACCELERATION_H

#include "path.h"
#include "accelerator.h"

class path_accelerationt
{
 public:
  virtual bool accelerate(patht &loop, path_acceleratort &accelerator) = 0;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ACCELERATION_H
