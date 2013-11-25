/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_BOOLEFORCE_H
#define CPROVER_SATCHECK_BOOLEFORCE_H

#include <vector>
#include <set>

#include "cnf.h"

class satcheck_booleforce_baset:public cnf_solvert
{
public:
  virtual ~satcheck_booleforce_baset();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
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

#endif
