/*******************************************************************\

Module: ILP structure

Author: Vincent Nimal

\*******************************************************************/

#ifdef HAVE_GLPK
#include <glpk.h>
#endif

#include <vector>

#ifndef ILP_H
#define ILP_H

#ifdef HAVE_GLPK
class ilpt 
{
protected:
  template <class T>
  class my_vectort: public std::vector<T> {
  public:
    T* to_array() {
      /* NOTE: not valid if T==bool */
      return &(*this)[0];
    }
  };

  glp_iocp parm;
  unsigned matrix_size;

public:
  glp_prob* lp;

  my_vectort<int> imat;
  my_vectort<int> jmat;
  my_vectort<double> vmat;

  ilpt () {
    glp_init_iocp(&parm);
    parm.msg_lev=GLP_MSG_OFF;
    parm.presolve=GLP_ON;

    lp=glp_create_prob();
    glp_set_prob_name(lp, "fence optimisation");
    glp_set_obj_dir(lp, GLP_MIN);
  }

  ~ilpt () {
    glp_delete_prob(lp);
  }

  void set_size(unsigned mat_size) {
     matrix_size=mat_size;
     imat.resize(mat_size+1);
     jmat.resize(mat_size+1);
     vmat.resize(mat_size+1);
  }

  void solve() {
    glp_load_matrix(lp, matrix_size, imat.to_array(), 
      jmat.to_array(), vmat.to_array());
    glp_intopt(lp, &parm);
  }
};
#else
class ilpt {};
#endif

#endif
