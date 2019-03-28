/*******************************************************************\

Module: Capability to check whether an expression is a reason for
        the solver returning UNSAT

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Capability to check whether an expression is a reason for
/// the solver returning UNSAT

#ifndef CPROVER_SOLVERS_CONFLICT_PROVIDER_H
#define CPROVER_SOLVERS_CONFLICT_PROVIDER_H

class exprt;

class conflict_providert
{
public:
  /// Returns true if an expression is in the final conflict leading to UNSAT.
  /// The argument can be a Boolean expression or something more
  /// solver-specific, e.g. a `literal_exprt`.
  virtual bool is_in_conflict(const exprt &) const = 0;

  virtual ~conflict_providert() = default;
};

#endif // CPROVER_SOLVERS_CONFLICT_PROVIDER_H
