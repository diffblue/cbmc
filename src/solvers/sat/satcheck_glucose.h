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
  satcheck_glucose_baset(T *, message_handlert &message_handler);
  virtual ~satcheck_glucose_baset();

  resultt prop_solve() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  // extra MiniSat feature: solve with assumptions
  void set_assumptions(const bvt &_assumptions) override;

  // extra MiniSat feature: default branching decision
  void set_polarity(literalt a, bool value);

  bool is_in_conflict(literalt a) const override;
  bool has_set_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }

protected:
  T *solver;

  void add_variables();
  bvt assumptions;
};

class satcheck_glucose_no_simplifiert:
  public satcheck_glucose_baset<Glucose::Solver>
{
public:
  explicit satcheck_glucose_no_simplifiert(message_handlert &message_handler);
  const std::string solver_text() override;
};

class satcheck_glucose_simplifiert:
  public satcheck_glucose_baset<Glucose::SimpSolver>
{
public:
  explicit satcheck_glucose_simplifiert(message_handlert &message_handler);
  const std::string solver_text() override;
  void set_frozen(literalt a) override;
  bool is_eliminated(literalt a) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H
