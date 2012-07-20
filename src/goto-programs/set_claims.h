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

void make_assertions_false(goto_functionst &goto_functions);
  
void label_claims(goto_functionst &goto_functions);

#endif
