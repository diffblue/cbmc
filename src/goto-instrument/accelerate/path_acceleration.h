#ifndef PATH_ACCELERATION_H
#define PATH_ACCELERATION_H

#include "path.h"
#include "accelerator.h"

class path_accelerationt {
 public:
  virtual bool accelerate(patht &loop, path_acceleratort &accelerator) = 0;
};

#endif // PATH_ACCELERATION_H
