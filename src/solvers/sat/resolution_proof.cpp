/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "resolution_proof.h"

#include <util/invariant.h>

#include <stack>

template<class T>
void resolution_prooft<T>::build_core(std::vector<bool> &in_core)
{
  PRECONDITION(!clauses.empty());

  std::stack<typename clausest::size_type> s;
  std::vector<bool> seen;

  seen.resize(clauses.size(), false);

  s.push(clauses.size()-1);

  while(!s.empty())
  {
    typename clausest::size_type c_id=s.top();
    s.pop();

    if(seen[c_id])
      continue;
    seen[c_id]=true;

    const T &c=clauses[c_id];

    if(c.is_root)
    {
      for(std::size_t i=0; i<c.root_clause.size(); i++)
      {
        unsigned v=c.root_clause[i].var_no();
        INVARIANT(
          v < in_core.size(), "variable number should be within bounds");
        in_core[v]=true;
      }
    }
    else
    {
      INVARIANT(
        c.first_clause_id < c_id,
        "id of the clause to be pushed onto the clause stack shall be smaller "
        "than the id of the current clause");
      s.push(c.first_clause_id);

      for(clauset::stepst::size_type i=0; i<c.steps.size(); i++)
      {
        // must decrease
        INVARIANT(
          c.steps[i].clause_id < c_id,
          "id of the clause to be pushed onto the clause stack shall be "
          "smaller than the id of the current clause");
        s.push(c.steps[i].clause_id);
      }
    }
  }
}

template class resolution_prooft<clauset>;
