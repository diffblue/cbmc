/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_QBF_QUBE_H
#define CPROVER_QBF_QUBE_H

#include "qdimacs_cnf.h"

class qbf_qubet:public qdimacs_cnft
{
public:
  qbf_qubet();
  virtual ~qbf_qubet();

  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
};

#endif
