/*******************************************************************\

Module: Capability to return assumptions that are in a conflict
        when solving under assumptions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Capability to return assumptions that are in a conflict
//  when solving under assumptions

#ifndef CPROVER_SOLVERS_PROP_SOLVER_CONFLICTS_H
#define CPROVER_SOLVERS_PROP_SOLVER_CONFLICTS_H

class literalt;

class solver_conflictst
{
public:
  /// Returns true if an assumption is in the final conflict
  virtual bool is_in_conflict(literalt) const = 0;

  virtual ~solver_conflictst() = default;
};

#endif // CPROVER_SOLVERS_PROP_SOLVER_CONFLICTS_H
