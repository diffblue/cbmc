/*******************************************************************\

Module: Symbol Table + CFG

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbol Table + CFG

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

  void output(std::ostream &out) const
  {
    namespacet ns(symbol_table);
    goto_functions.output(ns, out);
  }

  goto_modelt()
  {
  }

  // Copying is normally too expensive
  goto_modelt(const goto_modelt &)=delete;
  goto_modelt &operator=(const goto_modelt &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_modelt(goto_modelt &&other):
    symbol_table(std::move(other.symbol_table)),
    goto_functions(std::move(other.goto_functions))
  {
  }

  goto_modelt &operator=(goto_modelt &&other)
  {
    symbol_table=std::move(other.symbol_table);
    goto_functions=std::move(other.goto_functions);
    return *this;
  }
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
