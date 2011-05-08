/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_ZCORE_H
#define CPROVER_SATCHECK_ZCORE_H

#include <set>

#include "dimacs_cnf.h"

class satcheck_zcoret:public dimacs_cnft
{
public:
  satcheck_zcoret();
  virtual ~satcheck_zcoret();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
  
  bool is_in_core(literalt l) const
  {
    return in_core.find(l.var_no())!=in_core.end();
  }

protected:
  std::set<unsigned> in_core;
};

#endif
