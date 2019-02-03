/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_PBS_DIMACS_CNF_H
#define CPROVER_SOLVERS_SAT_PBS_DIMACS_CNF_H

#include <set>
#include <map>
#include <iosfwd>

#include "dimacs_cnf.h"

class pbs_dimacs_cnft:public dimacs_cnft
{
public:
  explicit pbs_dimacs_cnft(message_handlert &message_handler)
    : dimacs_cnft(message_handler),
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

  std::map<literalt, unsigned> pb_constraintmap;

  bool pbs_solve();

  resultt prop_solve() override;

  tvt l_get(literalt a) const override;

  // dummy functions

  const std::string solver_text() override
  {
    return "PBS - Pseudo Boolean/CNF Solver and Optimizer";
  }

protected:
  std::set<int> assigned;
};

#endif // CPROVER_SOLVERS_SAT_PBS_DIMACS_CNF_H
