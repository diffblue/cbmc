/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#ifndef CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H
#define CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H

#include <goto-instrument/contracts/utils.h>

/// Combine invariant of form
/// (in_inv || !guard) && (!guard -> pos_inv)
invariant_mapt combine_in_and_post_invariant_clauses(
  const invariant_mapt &in_clauses,
  const invariant_mapt &post_clauses,
  const invariant_mapt &neg_guards);

#endif // CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H
