/*******************************************************************\

Module: k-induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_K_INDUCTION_H
#define CPROVER_K_INDUCTION_H

#include <goto-programs/goto_functions.h>

void k_induction(
  goto_functionst &goto_functions,
  unsigned k,
  bool base_case, bool step_case);

#endif
