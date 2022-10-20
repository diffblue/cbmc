/*******************************************************************\

Module: Squolem Backend (with Proofs)

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Squolem Backend (with Proofs)

#ifndef CPROVER_SOLVERS_QBF_QBF_SQUOLEM_CORE_H
#define CPROVER_SOLVERS_QBF_QBF_SQUOLEM_CORE_H

#include <quannon/squolem2/squolem2.h>

#include "qdimacs_core.h"

class qbf_squolem_coret:public qdimacs_coret
{
protected:
  Squolem2 *squolem;
  bool early_decision;

public:
  qbf_squolem_coret();
  ~qbf_squolem_coret() override;

  std::string solver_text() const override;
  resultt prop_solve() override;

  tvt l_get(literalt a) const override;
  bool is_in_core(literalt l) const override;

  void set_debug_filename(const std::string &str);

  void lcnf(const bvt &bv) override;
  void add_quantifier(const quantifiert &quantifier) override;
  void set_quantifier(const quantifiert::typet type, const literalt l) override;
  void set_no_variables(size_t no) override;
  virtual size_t no_clauses() const { return squolem->clauses(); }

  modeltypet m_get(literalt a) const override;

  void write_qdimacs_cnf(std::ostream &out) override;

  void reset(void);

  const exprt f_get(literalt l) override;

private:
  typedef std::unordered_map<unsigned, exprt> function_cachet;
    function_cachet function_cache;

  const exprt f_get_cnf(WitnessStack *wsp);
  const exprt f_get_dnf(WitnessStack *wsp);

  void setup(void);
};

#endif // CPROVER_SOLVERS_QBF_QBF_SQUOLEM_CORE_H
