#include <iostream>

#include "enumerating_loop_acceleration.h"

//#define DEBUG

bool enumerating_loop_accelerationt::accelerate(
    path_acceleratort &accelerator) {
  patht path;
  int enumerated = 0;

  // Note: we use enumerated != path_limit rather than
  // enumerated < path_limit so that passing in path_limit=-1 causes
  // us to enumerate all the paths (or at least 2^31 of them...)
  while (path_enumerator->next(path) && enumerated++ != path_limit) {
#ifdef DEBUG
    std::cout << "Found a path..." << std::endl;
    namespacet ns(symbol_table);

    for (patht::iterator it = path.begin();
         it != path.end();
         ++it) {
      goto_program.output_instruction(ns, "OMG", std::cout, it->loc);
    }
#endif

    if (polynomial_accelerator.accelerate(path, accelerator)) {
      // We accelerated this path successfully -- return it.
#ifdef DEBUG
      std::cout << "Accelerated it" << std::endl;
#endif

      accelerator.path.swap(path);
      return true;
    }

    path.clear();
  }

  // No more paths, or we hit the enumeration limit.
#ifdef DEBUG
  std::cout << "No more paths to accelerate!" << std::endl;
#endif

  return false;
}
