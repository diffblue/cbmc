/*******************************************************************\

Module: Solver capability to set resource limits

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Solver capability to set resource limits

#ifndef CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
#define CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H

#include <cstdint>
#include <limits>

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
    // Saturate to UINT32_MAX milliseconds (~49.7 days) to avoid silently
    // wrapping for inputs greater than ~4.29 million seconds.
    const uint64_t ms = static_cast<uint64_t>(lim) * 1000u;
    set_time_limit_milliseconds(
      ms > std::numeric_limits<uint32_t>::max()
        ? std::numeric_limits<uint32_t>::max()
        : static_cast<uint32_t>(ms));
  }

  virtual ~solver_resource_limitst() = default;
};

#endif // CPROVER_SOLVERS_PROP_SOLVER_RESOURCE_LIMITS_H
