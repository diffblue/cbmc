/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/decision_procedure.h>

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

/*******************************************************************\

Function: path_symex_historyt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_historyt::convert(decision_proceduret &dest) const
{
  for(stepst::const_iterator s_it=steps.begin();
      s_it!=steps.end();
      s_it++)
  {
    if(s_it->ssa_rhs.is_not_nil())
      dest << equal_exprt(s_it->ssa_lhs, s_it->ssa_rhs);

    if(s_it->guard.is_not_nil())
      dest << s_it->guard;
  }
}
