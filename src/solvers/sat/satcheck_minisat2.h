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
  class SimpSolver;
}

// select one: basic solver or with simplification

#define USE_MINISAT_SIMPLIFIER

class satcheck_minisatt:public cnf_solvert
{
public:
  satcheck_minisatt();
  virtual ~satcheck_minisatt();
  
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
  #ifdef USE_MINISAT_SIMPLIFIER
  Minisat::SimpSolver *solver;
  #else
  Minisat::Solver *solver;
  #endif
  
  void add_variables();
  bvt assumptions;
  bool empty_clause_added;
};

#endif
