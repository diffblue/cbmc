/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

#ifndef CPROVER_ALIGNMENT_CHECKS_H
#define CPROVER_ALIGNMENT_CHECKS_H

#include <ostream>

#include <goto-programs/goto_functions.h>

void print_struct_alignment_problems(
  const symbol_tablet &symbol_table,
  std::ostream &out);

#endif
