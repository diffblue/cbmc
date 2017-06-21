/*******************************************************************\

Module: Branch Instrumentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Branch Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_BRANCH_H
#define CPROVER_GOTO_INSTRUMENT_BRANCH_H

#include <goto-programs/goto_functions.h>

void branch(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id);

#endif // CPROVER_GOTO_INSTRUMENT_BRANCH_H
