/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_SATCHECK_PICOSAT_H
#define CPROVER_SATCHECK_PICOSAT_H

#include "cnf.h"

class satcheck_picosatt:public cnf_solvert
{
public:
  satcheck_picosatt();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  virtual bool is_in_conflict(literalt a) const;
  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }

protected:
  bvt assumptions;
};

#endif
