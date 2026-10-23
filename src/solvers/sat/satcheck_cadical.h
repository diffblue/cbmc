/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H

#include <solvers/hardness_collector.h>

#include "cnf.h"

#include <chrono>
#include <cstdint>
#include <memory>

namespace CaDiCaL // NOLINT(readability/namespace)
{
class Solver;     // NOLINT(readability/identifiers)
class Terminator; // NOLINT(readability/identifiers)
}

class satcheck_cadical_baset : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_cadical_baset(
    int preprocessing_limit,
    int localsearch_limit,
    message_handlert &);
  virtual ~satcheck_cadical_baset();

  std::string solver_text() const override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  bool has_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }
  bool is_in_conflict(literalt a) const override;

#if 0
  literalt new_variable() override;
  bvt new_variables(std::size_t width) override;
#endif

  /// \copydoc propt::set_time_limit_milliseconds
  /// Implemented by registering a `CaDiCaL::Terminator` that returns
  /// true once the deadline has passed; the CaDiCaL solver polls the
  /// terminator during solving and aborts cleanly on a true return.
  void set_time_limit_milliseconds(uint32_t lim) override
  {
    time_limit_milliseconds = lim;
  }

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

  // NOLINTNEXTLINE(readability/identifiers)
  CaDiCaL::Solver *solver;
  int preprocessing_limit = 0, localsearch_limit = 0;

  uint32_t time_limit_milliseconds = 0;

  /// Concrete `CaDiCaL::Terminator` implementation that returns true
  /// once the per-solve deadline has been reached. Defined in the
  /// .cpp so the header can keep the CaDiCaL include out.
  class terminatort;
  std::unique_ptr<terminatort> terminator;
};

class satcheck_cadical_no_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_no_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(0, 0, message_handler)
  {
  }
};

class satcheck_cadical_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(1, 0, message_handler)
  {
  }
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
