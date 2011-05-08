/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/

#ifndef CPROVER_PBS_DIMACS_CNF_H
#define CPROVER_PBS_DIMACS_CNF_H

#include "dimacs_cnf.h"

#include <set>
#include <map>

#include <iostream>

class pbs_dimacs_cnft:public dimacs_cnft
{
 public:
  pbs_dimacs_cnft():
    optimize(false),
    maximize(false),
    binary_search(false),
    goal(0),
    opt_sum(0)
  {
  }

  virtual ~pbs_dimacs_cnft()
  {
  }
 
  virtual void write_dimacs_pb(std::ostream &out);

  bool optimize;
  bool maximize;
  bool binary_search;

  std::string pbs_path;

  int goal;
  int opt_sum;

  std::map<literalt,unsigned> pb_constraintmap;

  bool pbs_solve();

  virtual resultt prop_solve();

  virtual tvt l_get(literalt a) const;

  // dummy functions
  
  virtual const std::string solver_text()
    { return "PBS - Pseudo Boolean/CNF Solver and Optimizer"; }

 protected:

  std::set<int> assigned;
};

#endif
