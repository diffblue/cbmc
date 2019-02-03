/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H

#include "cnf.h"

namespace CaDiCaL // NOLINT(readability/namespace)
{
  class Solver; // NOLINT(readability/identifiers)
}

class satcheck_cadicalt:public cnf_solvert
{
public:
  satcheck_cadicalt();
  virtual ~satcheck_cadicalt();

  const std::string solver_text() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  void set_assumptions(const bvt &_assumptions) override;
  bool has_set_assumptions() const override
  {
    return false;
  }
  bool has_is_in_conflict() const override
  {
    return false;
  }
  bool is_in_conflict(literalt a) const override;

protected:
  resultt do_prop_solve() override;

  // NOLINTNEXTLINE(readability/identifiers)
  CaDiCaL::Solver * solver;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
