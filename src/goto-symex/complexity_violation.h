/*******************************************************************\

Module: Symbolic Execution

Author: John Dumbell

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_COMPLEXITY_VIOLATION_H
#define CPROVER_GOTO_SYMEX_COMPLEXITY_VIOLATION_H

/// What sort of symex-complexity violation has taken place.
///
/// Loop: If we've violated a loop complexity boundary, or are part of
/// a blacklisted loop.
/// Branch: If this particular branch has been deemed too complex.
enum class complexity_violationt
{
  NONE,
  LOOP,
  BRANCH,
};

#endif // CPROVER_GOTO_SYMEX_COMPLEXITY_VIOLATION_H
