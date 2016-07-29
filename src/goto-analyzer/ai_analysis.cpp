/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@kcs.ox.ac.uk

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include "ai_analysis.h"

  
/*******************************************************************\

Function: ai_analysist::eval

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

tvt ai_analysist::eval(goto_programt::const_targett t)
{
  exprt guard=t->guard;
  interval_domaint d=interval_analysis[t];

  //check whether the guard is a constant
  if (guard.is_true()) return tvt(true);

  //merge intervals to properly handle conjunction
  if (guard.id()==ID_and)
  {
    interval_domaint a(d);
    a.make_top();
    a.assume(guard,ns);

    #ifdef DEBUG
      a.output(std::cout, interval_analysis, ns);
      d.output(std::cout, interval_analysis, ns);
    #endif

    if (a.merge(d, t, t)) return tvt::unknown();
    return tvt(true);
  }
  else
  {
    d.assume(not_exprt(guard), ns);
    if(d.is_bottom()) return tvt(true);
    return tvt::unknown();
  }

}


/*******************************************************************\

Function: ai_analysist::show_intervals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_analysist::show_intervals(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  ait<interval_domaint> interval_analysis;

  if (constant_propagation)
    propagate_constants();

  interval_analysis(goto_model);
  interval_analysis.output(goto_model, out);
}

/*******************************************************************\

Function: ai_analysist::propagate_constants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_analysist::propagate_constants()
{
  status() << "propagating constants" << eom;

  Forall_goto_functions(f_it, goto_functions)
  {
    constant_propagator_ait(f_it->second,ns);
  }
}
