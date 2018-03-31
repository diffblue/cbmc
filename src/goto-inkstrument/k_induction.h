/*******************************************************************\

Module: k-induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// k-induction

#ifndef CPROVER_GOTO_INSTRUMENT_K_INDUCTION_H
#define CPROVER_GOTO_INSTRUMENT_K_INDUCTION_H

class goto_modelt;

void k_induction(
  goto_modelt &,
  bool base_case, bool step_case,
  unsigned k);

#endif // CPROVER_GOTO_INSTRUMENT_K_INDUCTION_H
