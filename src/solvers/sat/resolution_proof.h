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

  using stepst = std::vector<stept>;
  stepst steps;
};

template<class T=clauset>
class resolution_prooft
{
public:
  using clausest = std::vector<T>;
  clausest clauses;

  void build_core(std::vector<bool> &in_core);
};

using simple_prooft = resolution_prooft<clauset>;

#endif // CPROVER_SOLVERS_SAT_RESOLUTION_PROOF_H
