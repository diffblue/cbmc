/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_RESOLUTION_PROOF_H
#define CPROVER_SOLVERS_SAT_RESOLUTION_PROOF_H

#include <vector>

#include <solvers/prop/literal.h>

class clauset
{
public:
  bool is_root;
    
  // if root, what clause
  bvt root_clause;

  unsigned first_clause_id;

  struct stept
  {
    unsigned pivot_var_no;
    unsigned clause_id;
  };
    
  typedef std::vector<stept> stepst;
  stepst steps;
};

template<class T=clauset>
class resolution_prooft
{
public:
  typedef std::vector<T> clausest;
  clausest clauses;
  
  void build_core(std::vector<bool> &in_core);
};

typedef resolution_prooft<clauset> simple_prooft;

#endif
