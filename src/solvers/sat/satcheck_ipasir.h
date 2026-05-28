/*******************************************************************\

Module:

Author: Norbert Manthey, nmanthey@amazon.com

See \ref compilation-and-development-subsection-sat-solver for build
instructions.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
#define CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H

#include <solvers/hardness_collector.h>

#include "cnf.h"

#include <chrono>
#include <cstdint>

/// Interface for generic SAT solver interface IPASIR
class satcheck_ipasirt : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_ipasirt(message_handlert &message_handler);
  virtual ~satcheck_ipasirt() override;

  /// This method returns the description produced by the linked SAT solver
  std::string solver_text() const override;

  /// This method returns the truth value for a literal of the current SAT model
  tvt l_get(literalt a) const override final;

  void lcnf(const bvt &bv) override final;

  /* This method is not supported, and currently not called anywhere in CBMC */
  void set_assignment(literalt a, bool value) override;

  bool is_in_conflict(literalt a) const override;
  bool has_assumptions() const override final
  {
    return true;
  }
  bool has_is_in_conflict() const override final
  {
    return true;
  }

  /// \copydoc propt::set_time_limit_seconds
  /// Implemented by registering an `ipasir_set_terminate` callback that
  /// returns non-zero once the deadline has passed; IPASIR solvers poll
  /// the callback during solving and stop on a non-zero return.
  void set_time_limit_seconds(uint32_t lim) override
  {
    time_limit_seconds = lim;
  }

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

  void *solver;

  uint32_t time_limit_seconds = 0;
  std::chrono::steady_clock::time_point deadline;

  /// Static thunk passed to `ipasir_set_terminate`. Its `data` is the
  /// owning solver instance; returns 1 once the per-call deadline has
  /// been reached.
  static int terminate_callback(void *data);
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
