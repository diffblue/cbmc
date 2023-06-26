/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#include "synthesizer_utils.h"

invariant_mapt combine_in_and_post_invariant_clauses(
  const invariant_mapt &in_clauses,
  const invariant_mapt &post_clauses,
  const invariant_mapt &neg_guards)
{
  // Combine invariant
  // (in_inv || !guard) && (!guard -> pos_inv) for loops with loop guard
  // in_inv && pos_inv for loops without loop guard
  invariant_mapt result;
  for(const auto &in_clause : in_clauses)
  {
    const auto &id = in_clause.first;
    const auto &it_guard = neg_guards.find(id);

    // Unconditional loop or failed to get loop guard.
    if(it_guard == neg_guards.end())
    {
      result[id] = and_exprt(in_clause.second, post_clauses.at(id));
    }
    // Loops with loop guard.
    else
    {
      result[id] = and_exprt(
        or_exprt(it_guard->second, in_clause.second),
        implies_exprt(it_guard->second, post_clauses.at(id)));
    }
  }
  return result;
}
