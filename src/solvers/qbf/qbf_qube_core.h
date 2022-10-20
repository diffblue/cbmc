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
  explicit qbf_qube_coret(message_handlert &message_handler);
  ~qbf_qube_coret() override;

  std::string solver_text() const override;
  virtual resultt prop_solve();

  bool is_in_core(literalt l) const override;

  tvt l_get(literalt a) const override
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

  modeltypet m_get(literalt a) const override;

  const exprt f_get(literalt) override
  {
    INVARIANT(false, "qube does not support full certificates.");
  }
};

#endif // CPROVER_SOLVERS_QBF_QBF_QUBE_CORE_H
