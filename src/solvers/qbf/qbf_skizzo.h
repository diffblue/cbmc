/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_QBF_SKIZZO_H
#define CPROVER_QBF_SKIZZO_H

#include "qdimacs_cnf.h"

class qbf_skizzot:public qdimacs_cnft
{
public:
  qbf_skizzot();
  virtual ~qbf_skizzot();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
};

#endif
