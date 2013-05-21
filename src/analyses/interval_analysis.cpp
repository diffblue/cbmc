/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "interval_domain.h"
#include "interval_analysis.h"

/*******************************************************************\

Function: instrument_intervals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_intervals(
  const static_analysist<interval_domaint> &interval_analysis,
  goto_functionst::goto_functiont &goto_function)
{
  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    const interval_domaint &d=interval_analysis[i_it];

    exprt assertion=d.make_expression();
    if(!assertion.is_true())
    {
      goto_programt::targett t=i_it;
      goto_function.body.insert_before_swap(i_it);
      t->make_assumption(assertion);
      i_it++; // goes to original instruction
      t->location=i_it->location;
      t->function=i_it->function;
    }
  }
}

/*******************************************************************\

Function: interval_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_analysis(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  static_analysist<interval_domaint> interval_analysis(ns);

  Forall_goto_functions(f_it, goto_functions)
    instrument_intervals(interval_analysis, f_it->second);
}
