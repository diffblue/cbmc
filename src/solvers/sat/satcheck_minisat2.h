/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H
#define CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H

#include "cnf.h"

// Select one: basic solver or with simplification.
// Note that the solver with simplifier isn't really robust
// when used incrementally, as variables may disappear
// unless set to 'frozen'.

namespace Minisat // NOLINT(readability/namespace)
{
class Solver; // NOLINT(readability/identifiers)
class SimpSolver; // NOLINT(readability/identifiers)
}

template<typename T>
class satcheck_minisat2_baset:public cnf_solvert
{
public:
  explicit satcheck_minisat2_baset(T *);
  virtual ~satcheck_minisat2_baset();

  virtual resultt prop_solve() override;
  virtual tvt l_get(literalt a) const final;

  virtual void lcnf(const bvt &bv) final;
  virtual void set_assignment(literalt a, bool value) override;

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions) override;

  // extra MiniSat feature: default branching decision
  void set_polarity(literalt a, bool value);

  virtual bool is_in_conflict(literalt a) const override;
  virtual bool has_set_assumptions() const final { return true; }
  virtual bool has_is_in_conflict() const final { return true; }

  void set_time_limit_seconds(uint32_t lim) override
  {
    time_limit_seconds=lim;
  }

protected:
  T *solver;
  uint32_t time_limit_seconds;

  void add_variables();
  bvt assumptions;
};

class satcheck_minisat_no_simplifiert:
  public satcheck_minisat2_baset<Minisat::Solver>
{
public:
  satcheck_minisat_no_simplifiert();
  virtual const std::string solver_text();
};

class satcheck_minisat_simplifiert:
  public satcheck_minisat2_baset<Minisat::SimpSolver>
{
public:
  satcheck_minisat_simplifiert();
  virtual const std::string solver_text() final;
  virtual void set_frozen(literalt a) final;
  bool is_eliminated(literalt a) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H
