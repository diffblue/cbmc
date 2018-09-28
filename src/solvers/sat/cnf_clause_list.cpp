/*******************************************************************\

Module: CNF Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CNF Generation

#include "cnf_clause_list.h"

#include <ostream>

void cnf_clause_listt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  clauses.push_back(new_bv);
}

void cnf_clause_list_assignmentt::print_assignment(std::ostream &out) const
{
  for(unsigned v=1; v<assignment.size(); v++)
    out << "v" << v << "=" << assignment[v] << "\n";
}

void cnf_clause_list_assignmentt::copy_assignment_from(const propt &prop)
{
  assignment.resize(no_variables());

  // we don't use index 0, start with 1
  for(unsigned v=1; v<assignment.size(); v++)
  {
    literalt l;
    l.set(v, false);
    assignment[v]=prop.l_get(l);
  }
}
