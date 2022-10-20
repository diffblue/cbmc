/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_SKIZZO_H
#define CPROVER_SOLVERS_QBF_QBF_SKIZZO_H

#include "qdimacs_cnf.h"

class qbf_skizzot:public qdimacs_cnft
{
public:
  explicit qbf_skizzot(message_handlert &message_handler);
  ~qbf_skizzot() override;

  std::string solver_text() const override;
  virtual resultt prop_solve();
  tvt l_get(literalt a) const override;
};

#endif // CPROVER_SOLVERS_QBF_QBF_SKIZZO_H
