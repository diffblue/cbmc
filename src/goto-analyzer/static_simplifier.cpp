/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#include "static_simplifier.h"

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: static_simplifiert::simplify_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_simplifiert::simplify_guards(const bool constant_propagation)
{
  unsigned pass=0, fail=0, unknown=0;

  if (constant_propagation)
    propagate_constants();

  status() << "simplifying guards" << eom;
  interval_analysis(goto_functions, ns);

  Forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert() || i_it->is_assume()
        || i_it->is_goto())
      {
        tvt r=eval(i_it);

        if(r.is_true())
        {
          pass++;
    	  i_it->guard=true_exprt();
        }
        else if(r.is_false())
        {
          fail++;
    	  i_it->guard=false_exprt();
        }
        else
          unknown++;
      }
    }
  }
  status() << "SUMMARY: " << pass << " pass, " << fail << " fail, "
           << unknown << " unknown" << eom;
}
