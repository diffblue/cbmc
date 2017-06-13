/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H
#define CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H

#include <iosfwd>

#include <goto-programs/goto_functions.h>

void add_uninitialized_locals_assertions(
  class symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

void show_uninitialized(
  const class symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H
