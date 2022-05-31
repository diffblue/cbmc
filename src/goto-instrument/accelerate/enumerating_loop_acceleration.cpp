/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "enumerating_loop_acceleration.h"

#include "accelerator.h"

bool enumerating_loop_accelerationt::accelerate(
  path_acceleratort &accelerator)
{
  patht path;
  int enumerated = 0;

  // Note: we use enumerated!=path_limit rather than
  // enumerated < path_limit so that passing in path_limit=-1 causes
  // us to enumerate all the paths (or at least 2^31 of them...)
  while(path_enumerator->next(path) && enumerated++!=path_limit)
  {
#ifdef DEBUG
    std::cout << "Found a path...\n";
    namespacet ns(symbol_table);

    for(patht::iterator it = path.begin();
        it!=path.end();
        ++it)
    {
      it->loc->output(std::cout);
    }
#endif

    if(polynomial_accelerator.accelerate(path, accelerator))
    {
      // We accelerated this path successfully -- return it.
#ifdef DEBUG
      std::cout << "Accelerated it\n";
#endif

      accelerator.path.swap(path);
      return true;
    }

    path.clear();
  }

  // No more paths, or we hit the enumeration limit.
#ifdef DEBUG
  std::cout << "No more paths to accelerate!\n";
#endif

  return false;
}
