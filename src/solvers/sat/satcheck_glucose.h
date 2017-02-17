/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H
#define CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H

#include "cnf.h"

// Select one: basic solver or with simplification.
// Note that the solver with simplifier isn't really robust
// when used incrementally, as variables may disappear
// unless set to 'frozen'.

namespace Glucose // NOLINT(readability/namespace)
{
class Solver; // NOLINT(readability/identifiers)
class SimpSolver; // NOLINT(readability/identifiers)
}

template<typename T>
class satcheck_glucose_baset:public cnf_solvert
{
public:
  explicit satcheck_glucose_baset(T *);
  virtual ~satcheck_glucose_baset();

  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions);

  // extra MiniSat feature: default branching decision
  void set_polarity(literalt a, bool value);

  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }

protected:
  T *solver;

  void add_variables();
  bvt assumptions;
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

#endif // CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H
