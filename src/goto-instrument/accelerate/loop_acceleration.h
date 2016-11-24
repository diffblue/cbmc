#ifndef LOOP_ACCELERATION_H
#define LOOP_ACCELERATION_H

#include "path.h"
#include "accelerator.h"

class loop_accelerationt {
 public:
  virtual bool accelerate(path_acceleratort &accelerator) = 0;
};

#endif // LOOP_ACCELERATION_H
