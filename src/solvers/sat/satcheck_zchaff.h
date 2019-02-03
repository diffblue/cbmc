/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_ZCHAFF_H
#define CPROVER_SOLVERS_SAT_SATCHECK_ZCHAFF_H

#include "cnf_clause_list.h"

// use this only if you want to have something
// derived from CSolver
// otherwise, use satcheck_zchafft
// NOLINTNEXTLINE(readability/identifiers)
class CSolver;

class satcheck_zchaff_baset:public cnf_clause_listt
{
public:
  explicit satcheck_zchaff_baset(CSolver *_solver);
  virtual ~satcheck_zchaff_baset();

  const std::string solver_text() override;
  resultt prop_solve() override;
  tvt l_get(literalt a) const override;
  void set_assignment(literalt a, bool value) override;
  virtual void copy_cnf();

  CSolver *zchaff_solver()
  {
    return solver;
  }

protected:
  CSolver *solver;

  enum statust { INIT, SAT, UNSAT, ERROR };
  statust status;
};

class satcheck_zchafft:public satcheck_zchaff_baset
{
 public:
  satcheck_zchafft();
  virtual ~satcheck_zchafft();
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_ZCHAFF_H
