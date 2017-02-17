/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_LOOP_ACCELERATION_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_LOOP_ACCELERATION_H

#include "path.h"
#include "accelerator.h"

class loop_accelerationt
{
 public:
  virtual bool accelerate(path_acceleratort &accelerator) = 0;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_LOOP_ACCELERATION_H
