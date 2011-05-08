/*******************************************************************\

Module: Dump C from Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_DUMP_C_H
#define CPROVER_GOTO_PROGRAM_DUMP_C_H

#include "goto_functions.h"

void dump_c(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out);

#endif
