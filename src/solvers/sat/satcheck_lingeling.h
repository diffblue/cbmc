/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_LINGELING_H
#define CPROVER_SOLVERS_SAT_SATCHECK_LINGELING_H

#include "cnf.h"

// NOLINTNEXTLINE(readability/identifiers)
struct LGL;

class satcheck_lingelingt:public cnf_solvert
{
public:
  satcheck_lingelingt();
  virtual ~satcheck_lingelingt();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }
  virtual bool is_in_conflict(literalt a) const;
  virtual void set_frozen(literalt a);

protected:
  // NOLINTNEXTLINE(readability/identifiers)
  struct LGL * solver;
  bvt assumptions;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_LINGELING_H
