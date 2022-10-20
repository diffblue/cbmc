/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_QUBE_H
#define CPROVER_SOLVERS_QBF_QBF_QUBE_H

#include "qdimacs_cnf.h"

class qbf_qubet:public qdimacs_cnft
{
public:
  explicit qbf_qubet(message_handlert &message_handler);
  ~qbf_qubet() override;

  std::string solver_text() const override;
  virtual resultt prop_solve();
  tvt l_get(literalt a) const override;
};

#endif // CPROVER_SOLVERS_QBF_QBF_QUBE_H
