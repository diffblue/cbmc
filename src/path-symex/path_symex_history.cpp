/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/decision_procedure.h>

#include <langapi/language_util.h>

#include "path_symex_history.h"

/*******************************************************************\

Function: path_symex_stept::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_stept::output(std::ostream &out) const
{
  out << "PCs:";

/*
    for(pc_vectort::const_iterator p_it=s_it->pc_vector.begin();
        p_it!=pc_vector.end();
        p_it++)
      out << " " << *p_it;
 */     
  out << "\n";
  
  out << "Guard: " << from_expr(guard) << "\n";
  out << "Full LHS: " << from_expr(full_lhs) << "\n";
  out << "SSA LHS: " << from_expr(ssa_lhs) << "\n";
  out << "SSA RHS: " << from_expr(ssa_rhs) << "\n";
  out << "\n";
}

/*******************************************************************\

Function: path_symex_stept::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_stept::convert(decision_proceduret &dest) const
{
  if(ssa_rhs.is_not_nil())
    dest << equal_exprt(ssa_lhs, ssa_rhs);

  if(guard.is_not_nil())
    dest << guard;
}

/*******************************************************************\

Function: path_symex_step_reft::build_history

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_step_reft::build_history(
  std::vector<path_symex_step_reft> &dest) const
{
  dest.clear();

  path_symex_step_reft s=*this;
  while(!s.is_nil())
  {
    dest.push_back(s);
    --s;
  }
  
  // the above goes backwards: now need to reverse
  std::reverse(dest.begin(), dest.end());
}
