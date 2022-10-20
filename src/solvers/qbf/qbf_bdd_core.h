/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_BDD_CORE_H
#define CPROVER_SOLVERS_QBF_QBF_BDD_CORE_H

#include <vector>


#include "qdimacs_core.h"

class Cudd; // NOLINT(*)
class BDD; // NOLINT(*)

class qbf_bdd_certificatet:public qdimacs_coret
{
protected:
  Cudd *bdd_manager;

  typedef std::vector<BDD*> model_bddst;
  model_bddst model_bdds;

  typedef std::unordered_map<unsigned, exprt> function_cachet;
  function_cachet function_cache;

public:
  qbf_bdd_certificatet(void);
  ~qbf_bdd_certificatet(void) override;

  literalt new_variable(void) override;

  tvt l_get(literalt a) const override;
  const exprt f_get(literalt l) override;
};


class qbf_bdd_coret:public qbf_bdd_certificatet
{
private:
  typedef std::vector<BDD*> bdd_variable_mapt;
  bdd_variable_mapt bdd_variable_map;

  BDD *matrix;

public:
  qbf_bdd_coret();
  ~qbf_bdd_coret() override;

  literalt new_variable() override;

  void lcnf(const bvt &bv) override;
  literalt lor(literalt a, literalt b) override;
  literalt lor(const bvt &bv) override;

  std::string solver_text() const override;
  resultt prop_solve() override;
  tvt l_get(literalt a) const override;

  bool is_in_core(literalt l) const override;
  modeltypet m_get(literalt a) const override;

protected:
  void compress_certificate(void);
};

#endif // CPROVER_SOLVERS_QBF_QBF_BDD_CORE_H
