/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_QBF_QUANTOR_H
#define CPROVER_QBF_QUANTOR_H

#include "qdimacs_cnf.h"

class qbf_quantort:public qdimacs_cnft
{
public:
  qbf_quantort();
  virtual ~qbf_quantort();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
};

#endif
