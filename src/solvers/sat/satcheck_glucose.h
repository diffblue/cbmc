/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H
#define CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

// Select one: basic solver or with simplification.
// Note that the solver with simplifier isn't really robust
// when used incrementally, as variables may disappear
// unless set to 'frozen'.

namespace Glucose // NOLINT(readability/namespace)
{
class Solver; // NOLINT(readability/identifiers)
class SimpSolver; // NOLINT(readability/identifiers)
}

template <typename T>
class satcheck_glucose_baset : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_glucose_baset(T *, message_handlert &message_handler);

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

  void
  with_solver_hardness(std::function<void(solver_hardnesst &)> handler) override
  {
    if(solver_hardness.has_value())
    {
      handler(solver_hardness.value());
    }
  }

  void enable_hardness_collection() override
  {
    solver_hardness = solver_hardnesst{};
  }

protected:
  // This class needs to be inherited from, and inheriting classes need to
  // delete `solver` in their destructor.
  virtual ~satcheck_glucose_baset() = default;

  resultt do_prop_solve() override;

  T *solver;

  void add_variables();
  bvt assumptions;

  optionalt<solver_hardnesst> solver_hardness;
};

class satcheck_glucose_no_simplifiert:
  public satcheck_glucose_baset<Glucose::Solver>
{
public:
  explicit satcheck_glucose_no_simplifiert(message_handlert &message_handler);
  ~satcheck_glucose_no_simplifiert() override;
  const std::string solver_text() override;
};

class satcheck_glucose_simplifiert:
  public satcheck_glucose_baset<Glucose::SimpSolver>
{
public:
  explicit satcheck_glucose_simplifiert(message_handlert &message_handler);
  ~satcheck_glucose_simplifiert() override;
  const std::string solver_text() override;
  void set_frozen(literalt a) override;
  bool is_eliminated(literalt a) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_H
