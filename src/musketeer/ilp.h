/*******************************************************************\

Module: ILP structure

Author: Vincent Nimal

\*******************************************************************/

/// \file
/// ILP structure

#ifdef HAVE_GLPK
#include <glpk.h>
#endif

#include <vector>

#ifndef CPROVER_MUSKETEER_ILP_H
#define CPROVER_MUSKETEER_ILP_H

#ifdef HAVE_GLPK
class ilpt
{
protected:
  glp_iocp parm;
  unsigned matrix_size;

public:
  glp_prob *lp;

  std::vector<int> imat;
  std::vector<int> jmat;
  std::vector<double> vmat;

  ilpt()
  {
    glp_init_iocp(&parm);
    parm.msg_lev=GLP_MSG_OFF;
    parm.presolve=GLP_ON;

    lp=glp_create_prob();
    glp_set_prob_name(lp, "fence optimisation");
    glp_set_obj_dir(lp, GLP_MIN);
  }

  ~ilpt()
  {
    glp_delete_prob(lp);
  }

  void set_size(unsigned mat_size)
  {
     matrix_size=mat_size;
     imat.resize(mat_size+1);
     jmat.resize(mat_size+1);
     vmat.resize(mat_size+1);
  }

  void solve()
  {
    glp_load_matrix(lp, matrix_size, imat.data(),
      jmat.data(), vmat.data());
    glp_intopt(lp, &parm);
  }
};
#else
class ilpt {};
#endif

#endif // CPROVER_MUSKETEER_ILP_H
