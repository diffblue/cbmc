/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_MINISAT2_H
#define CPROVER_SATCHECK_MINISAT2_H

#include <vector>
#include <set>

#include "cnf.h"

namespace Minisat
{
  class Solver;
}

class satcheck_minisat_baset:public cnf_solvert
{
public:
  satcheck_minisat_baset():solver(NULL)
  {
    empty_clause_added=false;
  }
  
  virtual ~satcheck_minisat_baset();
  
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual const std::string solver_text();
  virtual void set_assignment(literalt a, bool value);

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions);

  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }
  
protected:
  Minisat::Solver *solver;
  void add_variables();
  bvt assumptions;
  bool empty_clause_added;
};

class satcheck_minisat_coret:public satcheck_minisat_baset
{
public:
  satcheck_minisat_coret();
  virtual const std::string solver_text();
};

class satcheck_minisat_simpt:public satcheck_minisat_baset
{
public:
  satcheck_minisat_simpt();
  virtual const std::string solver_text();
};

#endif
