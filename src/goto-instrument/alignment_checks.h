/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

/// \file
/// Alignment Checks

#ifndef CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
#define CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H

#include <iosfwd>

class symbol_tablet;

void print_struct_alignment_problems(
  const symbol_tablet &symbol_table,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
