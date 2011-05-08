/*******************************************************************\

Module: Set claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SET_CLAIMS_H
#define CPROVER_GOTO_PROGRAMS_SET_CLAIMS_H

#include <goto-programs/goto_functions.h>

void set_claims(
  goto_functionst &goto_functions,
  const std::list<std::string> &claims);

void set_claims(
  goto_programt &goto_program,
  const std::list<std::string> &claims);

#endif
