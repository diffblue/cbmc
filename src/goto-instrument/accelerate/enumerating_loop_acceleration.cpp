#include "enumerating_loop_acceleration.h"

bool enumerating_loop_accelerationt::accelerate(
    path_acceleratort &accelerator) {
  patht path;

  while (path_enumerator.next(path)) {
    if (polynomial_accelerator.accelerate(path, accelerator)) {
      // We accelerated this path successfully -- return it.
      accelerator.path.swap(path);
      return true;
    }
  }

  // No more paths!
  return false;
}
