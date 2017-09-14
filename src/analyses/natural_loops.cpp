/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Dominators

#include "natural_loops.h"

#include <iostream>

void show_natural_loops(const goto_modelt &goto_model)
{
  forall_goto_functions(it, goto_model.goto_functions)
  {
    std::cout << "*** " << it->first << '\n';

    natural_loopst natural_loops;
    natural_loops(it->second.body);
    natural_loops.output(std::cout);

    std::cout << '\n';
  }
}
