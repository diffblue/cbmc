/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

namespace CaDiCaL // NOLINT(readability/namespace)
{
  class Solver; // NOLINT(readability/identifiers)
}

class satcheck_cadicalt : public cnf_solvert, public hardness_collectort
{
public:
  explicit satcheck_cadicalt(message_handlert &message_handler);
  virtual ~satcheck_cadicalt();

  const std::string solver_text() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  void set_assumptions(const bvt &_assumptions) override;
  bool has_set_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }
  bool is_in_conflict(literalt a) const override;

protected:
  resultt do_prop_solve() override;

  // NOLINTNEXTLINE(readability/identifiers)
  CaDiCaL::Solver * solver;

  bvt assumptions;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
