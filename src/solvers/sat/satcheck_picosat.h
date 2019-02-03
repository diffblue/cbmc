/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_PICOSAT_H
#define CPROVER_SOLVERS_SAT_SATCHECK_PICOSAT_H

#include "cnf.h"

// NOLINTNEXTLINE(readability/identifiers)
struct PicoSAT;

class satcheck_picosatt:public cnf_solvert
{
public:
  satcheck_picosatt();
  ~satcheck_picosatt();

  const std::string solver_text() override;
  resultt prop_solve() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  bool is_in_conflict(literalt a) const override;
  void set_assumptions(const bvt &_assumptions) override;
  bool has_set_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }

protected:
  bvt assumptions;

private:
  PicoSAT *picosat;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_PICOSAT_H
