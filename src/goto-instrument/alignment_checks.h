/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
#define CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H

#include <iosfwd>

#include <goto-programs/goto_functions.h>

void print_struct_alignment_problems(
  const symbol_tablet &symbol_table,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
