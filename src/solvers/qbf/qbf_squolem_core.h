/*******************************************************************\

Module: Squolem Backend (with Proofs)

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_QBF_SQUOLEM_CORE_H
#define CPROVER_QBF_SQUOLEM_CORE_H

#include <util/hash_cont.h>
#include <quannon/squolem2/squolem2.h>

#include "qdimacs_core.h"

class qbf_squolem_coret:public qdimacs_coret
{
protected:
  Squolem2* squolem;
  bool early_decision;

public:
  qbf_squolem_coret();
  virtual ~qbf_squolem_coret();

  virtual const std::string solver_text();
  virtual resultt prop_solve();

  virtual tvt l_get(literalt a) const;
  virtual bool is_in_core(literalt l) const;

  void set_debug_filename(const std::string &str);

  virtual void lcnf(const bvt &bv);
  virtual void add_quantifier(const quantifiert &quantifier);
  virtual void set_quantifier(const quantifiert::typet type, const literalt l);
  virtual void set_no_variables(unsigned no);
  virtual unsigned no_clauses() const { return squolem->clauses(); }

  virtual modeltypet m_get(literalt a) const;

  virtual void write_qdimacs_cnf(std::ostream &out);

  void reset(void);

  virtual const exprt f_get(literalt l);

private:
  typedef hash_map_cont<unsigned, exprt> function_cachet;
    function_cachet function_cache;

  const exprt f_get_cnf(WitnessStack *wsp);
  const exprt f_get_dnf(WitnessStack *wsp);

  void setup(void);
};

#endif /*_CPROVER_QBF_SQUOLEM_CORE_H_*/
