/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#include "static_simplifier.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: static_simplifiert::simplify_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_simplifiert::simplify_guards()
{
  unsigned simplified[]={0,0,0}, unknown[]={0,0,0};

  if (constant_propagation)
    propagate_constants();

  if (intervals)
    interval_analysis(goto_functions, ns);

  status() << "simplifying guards" << eom;

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
    	  i_it->guard=true_exprt();
        else if(r.is_false())
    	  i_it->guard=false_exprt();

        //summarize the simplification results
        if (r.is_true() || r.is_false())
        {
      	  if (i_it->is_assert())
      	    simplified[0]+=1;
      	  else if (i_it->is_assume())
      		simplified[1]+=1;
      	  else
      		simplified[2]+=1;
        }
        else
        {
       	  if (i_it->is_assert())
       		unknown[0]+=1;
       	  else if (i_it->is_assume())
       		unknown[1]+=1;
       	  else
       		unknown[2]+=1;
        }
      }
    }
  }
  status() << "SIMPLIFIED: " << " assert: " << simplified[0]
		   << ", assume: " << simplified[1]
		   << ", goto: " << simplified[2] << "\n"
		   << "UNKNOWN: " << "    assert: " << unknown[0]
		   << ", assume: " << unknown[1]
		   << ", goto: " << unknown[2] << eom;

  //make sure the references are correct
  goto_functions.update();
}
