/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_MINISAT_H
#define CPROVER_SOLVERS_SAT_SATCHECK_MINISAT_H

#include <vector>

#include "cnf.h"
#include "resolution_proof.h"

class satcheck_minisat1_baset:public cnf_solvert
{
public:
  satcheck_minisat1_baset():solver(NULL)
  {
  }

  virtual ~satcheck_minisat1_baset();

  virtual const std::string solver_text() override;
  virtual resultt prop_solve() override;
  virtual tvt l_get(literalt a) const override;

  virtual void lcnf(const bvt &bv) final;

  virtual void set_assignment(literalt a, bool value) override;

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions) override;

  // features
  virtual bool has_set_assumptions() const override { return true; }
  virtual bool has_is_in_conflict() const override { return true; }

  virtual bool is_in_conflict(literalt l) const override;

protected:
  // NOLINTNEXTLINE(readability/identifiers)
  class Solver *solver;
  void add_variables();
  bvt assumptions;
  bool empty_clause_added;
};

class satcheck_minisat1t:public satcheck_minisat1_baset
{
public:
  satcheck_minisat1t();
};

class satcheck_minisat1_prooft:public satcheck_minisat1t
{
public:
  satcheck_minisat1_prooft();
  ~satcheck_minisat1_prooft();

  virtual const std::string solver_text() override;
  simple_prooft &get_resolution_proof();
  // void set_partition_id(unsigned p_id);

protected:
  // NOLINTNEXTLINE(readability/identifiers)
  class Proof *proof;
  class minisat_prooft *minisat_proof;
};

class satcheck_minisat1_coret:public satcheck_minisat1_prooft
{
public:
  satcheck_minisat1_coret();
  ~satcheck_minisat1_coret();

  virtual const std::string solver_text() override;
  virtual resultt prop_solve() override;

  virtual bool has_in_core() const { return true; }

  virtual bool is_in_core(literalt l) const
  {
    PRECONDITION(l.var_no() < in_core.size());
    return in_core[l.var_no()];
  }

protected:
  std::vector<bool> in_core;
};
#endif // CPROVER_SOLVERS_SAT_SATCHECK_MINISAT_H
