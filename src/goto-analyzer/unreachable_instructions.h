/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_UNREACHABLE_INSTRUCTIONS_H
#define CPROVER_UNREACHABLE_INSTRUCTIONS_H

#include <ostream>

class goto_modelt;

void unreachable_instructions(
  const goto_modelt &,
  const bool json,
  std::ostream &os);

#endif
