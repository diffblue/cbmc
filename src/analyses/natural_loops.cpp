/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#include <iostream>

#include "natural_loops.h"

//#define DEBUG

/*******************************************************************\

Function: show_natural_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_natural_loops(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
  {
    std::cout << "*** " << it->first << std::endl;

    natural_loopst natural_loops;
    natural_loops(it->second.body);
    natural_loops.output(std::cout);
    
    std::cout << std::endl;
  }
}

