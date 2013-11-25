/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_GLUCOSE_H
#define CPROVER_SATCHECK_GLUCOSE_H

#include "cnf.h"

// Select one: basic solver or with simplification.
// Note that the solver with simplifier isn't really robust
// when used incrementally, as variables may disappear
// unless set to 'frozen'.

namespace Glucose
{
  class Solver;
  class SimpSolver;
}

template<typename T>
class satcheck_glucose_baset:public cnf_solvert
{
public:
  satcheck_glucose_baset();
  virtual ~satcheck_glucose_baset();
  
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  // extra MiniSat/Glucose feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions);

  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }
  
protected:
  T *solver;
  
  void add_variables();
  bvt assumptions;
  bool empty_clause_added;
};

class satcheck_glucose_no_simplifiert:
  public satcheck_glucose_baset<Glucose::Solver>
{
public:
  satcheck_glucose_no_simplifiert();
  virtual const std::string solver_text();
};

class satcheck_glucose_simplifiert:
  public satcheck_glucose_baset<Glucose::SimpSolver>
{
public:
  satcheck_glucose_simplifiert();
  virtual const std::string solver_text();
  virtual void set_frozen(literalt a);
  bool is_eliminated(literalt a) const;
};

#endif
