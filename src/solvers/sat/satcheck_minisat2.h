/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H
#define CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

// Select one: basic solver or with simplification.
// Note that the solver with simplifier isn't really robust
// when used incrementally, as variables may disappear
// unless set to 'frozen'.

namespace Minisat // NOLINT(readability/namespace)
{
class Solver; // NOLINT(readability/identifiers)
class SimpSolver; // NOLINT(readability/identifiers)
}

template <typename T>
class satcheck_minisat2_baset : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_minisat2_baset(T *, message_handlert &message_handler);

  tvt l_get(literalt a) const override final;

  void lcnf(const bvt &bv) override final;
  void set_assignment(literalt a, bool value) override;

  // extra MiniSat feature: solve with assumptions
  void set_assumptions(const bvt &_assumptions) override;

  // extra MiniSat feature: default branching decision
  void set_polarity(literalt a, bool value);

  // extra MiniSat feature: interrupt running SAT query
  void interrupt();

  // extra MiniSat feature: permit previously interrupted SAT query to continue
  void clear_interrupt();

  bool is_in_conflict(literalt a) const override;
  bool has_set_assumptions() const override final
  {
    return true;
  }
  bool has_is_in_conflict() const override final
  {
    return true;
  }

  void set_time_limit_seconds(uint32_t lim) override
  {
    time_limit_seconds=lim;
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
  virtual ~satcheck_minisat2_baset() = default;

  resultt do_prop_solve() override;

  T *solver;
  uint32_t time_limit_seconds;

  void add_variables();
  bvt assumptions;

  optionalt<solver_hardnesst> solver_hardness;
};

class satcheck_minisat_no_simplifiert:
  public satcheck_minisat2_baset<Minisat::Solver>
{
public:
  explicit satcheck_minisat_no_simplifiert(message_handlert &message_handler);
  ~satcheck_minisat_no_simplifiert() override;
  const std::string solver_text() override;
};

class satcheck_minisat_simplifiert:
  public satcheck_minisat2_baset<Minisat::SimpSolver>
{
public:
  explicit satcheck_minisat_simplifiert(message_handlert &message_handler);
  ~satcheck_minisat_simplifiert() override;
  const std::string solver_text() override final;
  void set_frozen(literalt a) override final;
  bool is_eliminated(literalt a) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_MINISAT2_H
