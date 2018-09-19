/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_QUBE_CORE_H
#define CPROVER_SOLVERS_QBF_QBF_QUBE_CORE_H

#include "qdimacs_core.h"

#include <util/invariant.h>

class qbf_qube_coret:public qdimacs_coret
{
protected:
  std::string qbf_tmp_file;

  typedef std::map<unsigned, bool> assignmentt;
  assignmentt assignment;

public:
  qbf_qube_coret();
  virtual ~qbf_qube_coret();

  virtual const std::string solver_text();
  virtual resultt prop_solve();

  virtual bool is_in_core(literalt l) const;

  virtual tvt l_get(literalt a) const
  {
    unsigned v=a.var_no();

    assignmentt::const_iterator fit=assignment.find(v);

    if(fit!=assignment.end())
      return a.sign()?tvt(!fit->second) : tvt(fit->second);
    else
    {
      // throw "Missing toplevel assignment from QuBE";
      // We assume this is a don't-care and return unknown
    }


    return tvt::unknown();
  }

  virtual modeltypet m_get(literalt a) const;

  virtual const exprt f_get(literalt)
  {
    INVARIANT(false, "qube does not support full certificates.");
  }
};

#endif // CPROVER_SOLVERS_QBF_QBF_QUBE_CORE_H
