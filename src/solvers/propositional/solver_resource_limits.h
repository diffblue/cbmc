/*******************************************************************\

Module: Solver capability to set resource limits

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Solver capability to set resource limits

#ifndef CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
#define CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H

class solver_resource_limitst
{
public:
  /// Set the limit for the solver to time out in seconds
  virtual void set_time_limit_seconds(uint32_t) = 0;

  virtual ~solver_resource_limitst() = default;
};

#endif // CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
