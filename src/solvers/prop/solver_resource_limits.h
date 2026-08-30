/*******************************************************************\

Module: Solver capability to set resource limits

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Solver capability to set resource limits

#ifndef CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
#define CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H

#include <cstdint>

class solver_resource_limitst
{
public:
  /// Set a wall-clock time limit for each solver call, in
  /// milliseconds. A value of 0 disables the time limit. Granularity
  /// is best-effort: back-ends may round up or, where the underlying
  /// solver does not support timeouts, log a warning and ignore the
  /// limit.
  virtual void set_time_limit_milliseconds(uint32_t) = 0;

  /// Helper accepting a time limit in whole seconds; forwards to
  /// `set_time_limit_milliseconds` after multiplying by 1000.
  /// Provided for backward compatibility with callers that still
  /// express the limit in seconds (e.g. dependent projects predating
  /// the millisecond-precision rework).
  void set_time_limit_seconds(uint32_t lim)
  {
    set_time_limit_milliseconds(lim * 1000);
  }

  virtual ~solver_resource_limitst() = default;
};

#endif // CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
