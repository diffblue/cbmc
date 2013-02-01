/*******************************************************************\

Module: Symbol Table + CFG

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_MODEL_H
#define CPROVER_GOTO_MODEL_H

#include "goto_functions.h"

// A model is a pair consisting of a symbol table
// and the CFGs for the functions.

class goto_modelt
{
public:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  
  goto_modelt(
    const namespacet &_ns,
    const goto_functionst &_goto_functions):
    ns(_ns),
    goto_functions(_goto_functions)
  {
  }
};

#endif
