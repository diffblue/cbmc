/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

/// \file
/// Alignment Checks

#ifndef CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
#define CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H

#include <iosfwd>

class symbol_table_baset;

void print_struct_alignment_problems(
  const symbol_table_baset &symbol_table,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_ALIGNMENT_CHECKS_H
