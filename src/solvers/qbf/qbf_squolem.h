/*******************************************************************\

Module: Squolem Backend

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Squolem Backend

#ifndef CPROVER_SOLVERS_QBF_QBF_SQUOLEM_H
#define CPROVER_SOLVERS_QBF_QBF_SQUOLEM_H

#include <quannon/squolem2/squolem2.h>

#include "qdimacs_cnf.h"

class qbf_squolemt:public qdimacs_cnft
{
protected:
  Squolem2 squolem;
  bool early_decision;

public:
  qbf_squolemt();
  virtual ~qbf_squolemt();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void add_quantifier(const quantifiert &quantifier);
  virtual void set_quantifier(const quantifiert::typet type, const literalt l);
  virtual void set_no_variables(size_t no);
  virtual size_t no_clauses() const { return squolem.clauses(); }
};

#endif // CPROVER_SOLVERS_QBF_QBF_SQUOLEM_H
