/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <stack>

#include "resolution_proof.h"

/*******************************************************************\

Function: resolution_prooft::build_core

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
template<class T>
void resolution_prooft<T>::build_core(std::vector<bool> &in_core)
{
  std::stack<unsigned> s;
  std::vector<bool> seen;

  assert(!clauses.empty());
  
  seen.resize(clauses.size(), false);
  
  s.push(clauses.size()-1);
  
  while(!s.empty())
  {
    unsigned int c_id=s.top();
    s.pop();

    if(seen[c_id]) continue;
    seen[c_id]=true;
    
    const T &c=clauses[c_id];
    
    if(c.is_root)
    {
      for(unsigned i=0; i<c.root_clause.size(); i++)
      {
        unsigned v=c.root_clause[i].var_no();
        assert(v<in_core.size());
        in_core[v]=true;
      }
    }
    else
    {
      assert(c.first_clause_id<c_id);
      s.push(c.first_clause_id);

      for(unsigned i=0; i<c.steps.size(); i++)
      {
        // must decrease
        assert(c.steps[i].clause_id<c_id);
        s.push(c.steps[i].clause_id);
      }
    }
  }
}

template class resolution_prooft<clauset>;
