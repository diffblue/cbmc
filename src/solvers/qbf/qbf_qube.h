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
  virtual ~qbf_qubet();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
};

#endif // CPROVER_SOLVERS_QBF_QBF_QUBE_H
