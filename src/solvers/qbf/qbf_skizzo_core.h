/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_QBF_SKIZZO_CORE_H
#define CPROVER_QBF_SKIZZO_CORE_H

#include "qbf_bdd_core.h"

class qbf_skizzo_coret :
  public qbf_bdd_certificatet // a qdimacs_coret with f_get from BDDs
{
public:
  qbf_skizzo_coret();
  virtual ~qbf_skizzo_coret();

  virtual const std::string solver_text();
  virtual resultt prop_solve();

  virtual bool is_in_core(literalt l) const;
  virtual modeltypet m_get(literalt a) const;

protected:
  std::string qbf_tmp_file;

  bool get_certificate(void);
};

#endif
