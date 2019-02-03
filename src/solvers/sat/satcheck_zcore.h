/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_ZCORE_H
#define CPROVER_SOLVERS_SAT_SATCHECK_ZCORE_H

#include <set>

#include "dimacs_cnf.h"

class satcheck_zcoret:public dimacs_cnft
{
public:
  satcheck_zcoret();
  virtual ~satcheck_zcoret();

  const std::string solver_text() override;
  resultt prop_solve() override;
  tvt l_get(literalt a) const override;

  bool is_in_core(literalt l) const
  {
    return in_core.find(l.var_no())!=in_core.end();
  }

protected:
  std::set<unsigned> in_core;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_ZCORE_H
