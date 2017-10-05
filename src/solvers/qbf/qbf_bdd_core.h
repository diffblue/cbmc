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

  using model_bddst = std::vector<BDD*>;
  model_bddst model_bdds;

  using function_cachet = std::unordered_map<unsigned, exprt>;
  function_cachet function_cache;

public:
  qbf_bdd_certificatet(void);
  virtual ~qbf_bdd_certificatet(void);

  virtual literalt new_variable(void);

  virtual tvt l_get(literalt a) const;
  virtual const exprt f_get(literalt l);
};


class qbf_bdd_coret:public qbf_bdd_certificatet
{
private:
  using bdd_variable_mapt = std::vector<BDD*>;
  bdd_variable_mapt bdd_variable_map;

  BDD *matrix;

public:
  qbf_bdd_coret();
  virtual ~qbf_bdd_coret();

  virtual literalt new_variable();

  virtual void lcnf(const bvt &bv);
  virtual literalt lor(literalt a, literalt b);
  virtual literalt lor(const bvt &bv);

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual bool is_in_core(literalt l) const;
  virtual modeltypet m_get(literalt a) const;

protected:
  void compress_certificate(void);
};

#endif // CPROVER_SOLVERS_QBF_QBF_BDD_CORE_H
