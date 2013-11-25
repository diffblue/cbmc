/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_LIMMAT_H
#define CPROVER_SATCHECK_LIMMAT_H

#include <vector>
#include "dimacs_cnf.h"

class satcheck_limmatt:public dimacs_cnft
{
 public:
  satcheck_limmatt();
  virtual ~satcheck_limmatt();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  void copy_cnf();
  
 protected:
  struct Limmat *solver;
  std::vector<unsigned char> assignment;
};

#endif
