/*******************************************************************\

Module: Symbol Table + CFG

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H

#include <util/symbol_table.h>

#include "goto_functions.h"

// A model is a pair consisting of a symbol table
// and the CFGs for the functions.

class goto_modelt
{
public:
  symbol_tablet symbol_table;
  goto_functionst goto_functions;

  void clear()
  {
    symbol_table.clear();
    goto_functions.clear();
  }

  void output(std::ostream &out)
  {
    namespacet ns(symbol_table);
    goto_functions.output(ns, out);
  }

  goto_modelt()
  {
  }

  goto_modelt(goto_modelt &&other)
  {
    symbol_table.swap(other.symbol_table);
    goto_functions.swap(other.goto_functions);
  }

  // copying is likely too expensive
  goto_modelt(const goto_modelt &) = delete;
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
