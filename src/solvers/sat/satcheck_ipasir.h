/*******************************************************************\

Module:

Author: Norbert Manthey, nmanthey@amazon.com

See \ref compilation-and-development-subsection-sat-solver for build
instructions.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
#define CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

/// Interface for generic SAT solver interface IPASIR
class satcheck_ipasirt : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_ipasirt(message_handlert &message_handler);
  virtual ~satcheck_ipasirt() override;

  /// This method returns the description produced by the linked SAT solver
  const std::string solver_text() override;

  /// This method returns the truth value for a literal of the current SAT model
  tvt l_get(literalt a) const override final;

  void lcnf(const bvt &bv) override final;

  /* This method is not supported, and currently not called anywhere in CBMC */
  void set_assignment(literalt a, bool value) override;

  void set_assumptions(const bvt &_assumptions) override;

  bool is_in_conflict(literalt a) const override;
  bool has_set_assumptions() const override final
  {
    return true;
  }
  bool has_is_in_conflict() const override final
  {
    return true;
  }

protected:
  resultt do_prop_solve() override;

  void *solver;

  bvt assumptions;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
