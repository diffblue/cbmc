/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

#ifndef CPROVER_ALIGNMENT_CHECKS_H
#define CPROVER_ALIGNMENT_CHECKS_H

#include <iostream>

#include <goto-programs/goto_functions.h>

void print_struct_alignment_problems(
  const contextt &context,
  std::ostream &out);

#endif
