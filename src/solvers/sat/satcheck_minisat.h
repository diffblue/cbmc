/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_MINISAT_H
#define CPROVER_SATCHECK_MINISAT_H

#include <vector>
#include <set>

#include "cnf.h"
#include "resolution_proof.h"

class satcheck_minisat1_baset:public cnf_solvert
{
public:
  satcheck_minisat1_baset():solver(NULL)
  {
  }
  
  virtual ~satcheck_minisat1_baset();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  
  virtual void set_assignment(literalt a, bool value);

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions);

  // features  
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }
  
  virtual bool is_in_conflict(literalt l) const;
  
protected:
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
  
  virtual const std::string solver_text();
  simple_prooft &get_resolution_proof();
  //void set_partition_id(unsigned p_id);

protected:
  class Proof *proof;
  class minisat_prooft *minisat_proof;
};

class satcheck_minisat1_coret:public satcheck_minisat1_prooft
{
public:
  satcheck_minisat1_coret();
  ~satcheck_minisat1_coret();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  
  virtual bool has_in_core() const { return true; }
  
  virtual bool is_in_core(literalt l) const
  {
    assert(l.var_no()<in_core.size());
    return in_core[l.var_no()];
  }
  
protected:
  std::vector<bool> in_core;
};
#endif
