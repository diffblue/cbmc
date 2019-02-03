/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_BOOLEFORCE_H
#define CPROVER_SOLVERS_SAT_SATCHECK_BOOLEFORCE_H

#include <vector>
#include <set>

#include "cnf.h"

class satcheck_booleforce_baset:public cnf_solvert
{
public:
  virtual ~satcheck_booleforce_baset();

  const std::string solver_text() override;
  resultt prop_solve() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
};

class satcheck_booleforcet:public satcheck_booleforce_baset
{
public:
  satcheck_booleforcet();
};

class satcheck_booleforce_coret:public satcheck_booleforce_baset
{
public:
  satcheck_booleforce_coret();

  bool is_in_core(literalt l) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_BOOLEFORCE_H
