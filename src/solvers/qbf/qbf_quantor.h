/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_QUANTOR_H
#define CPROVER_SOLVERS_QBF_QBF_QUANTOR_H

#include "qdimacs_cnf.h"

class qbf_quantort:public qdimacs_cnft
{
public:
  explicit qbf_quantort(message_handlert &message_handler);
  virtual ~qbf_quantort();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
};

#endif // CPROVER_SOLVERS_QBF_QBF_QUANTOR_H
