/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_SATCHECK_PRECOSAT_H
#define CPROVER_SATCHECK_PRECOSAT_H

#include "cnf.h"

namespace PrecoSat
{
  class Solver;
}

class satcheck_precosatt:public cnf_solvert
{
public:
  satcheck_precosatt();
  virtual ~satcheck_precosatt();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  // PicoSAT has this, PrecoSAT doesn't
  // virtual bool is_in_conflict(literalt a) const;
  // virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return false; }
  virtual bool has_is_in_conflict() const { return false; }

protected:
  PrecoSat::Solver *solver;
  // bvt assumptions;
};

#endif
