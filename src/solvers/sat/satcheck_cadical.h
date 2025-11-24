/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

namespace CaDiCaL // NOLINT(readability/namespace)
{
  class Solver; // NOLINT(readability/identifiers)
}

class satcheck_cadical_baset : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_cadical_baset(
    int preprocessing_limit,
    int localsearch_limit,
    message_handlert &);
  virtual ~satcheck_cadical_baset();

  std::string solver_text() const override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  bool has_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }
  bool is_in_conflict(literalt a) const override;

#if 0
  literalt new_variable() override;
  bvt new_variables(std::size_t width) override;
#endif

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

  // NOLINTNEXTLINE(readability/identifiers)
  CaDiCaL::Solver *solver;
  int preprocessing_limit = 0, localsearch_limit = 0;
};

class satcheck_cadical_no_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_no_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(0, 0, message_handler)
  {
  }
};

class satcheck_cadical_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(1, 0, message_handler)
  {
  }
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
