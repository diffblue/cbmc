/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/language_util.h>

#include "path_symex_history.h"

/*******************************************************************\

Function: path_symex_historyt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_historyt::output(std::ostream &out) const
{
  for(stepst::const_iterator s_it=steps.begin();
      s_it!=steps.end();
      s_it++)
  {
    out << "PCs:";

/*
    for(pc_vectort::const_iterator p_it=s_it->pc_vector.begin();
        p_it!=pc_vector.end();
        p_it++)
      out << " " << *p_it;
 */     
    out << "\n";
    
    out << "Guard: " << from_expr(s_it->guard) << "\n";
    out << "Full LHS: " << from_expr(s_it->full_lhs) << "\n";
    out << "SSA LHS: " << from_expr(s_it->ssa_lhs) << "\n";
    out << "SSA RHS: " << from_expr(s_it->ssa_rhs) << "\n";
    out << "\n";
  }
}
