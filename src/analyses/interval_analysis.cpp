/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/find_symbols.h>

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
  std::set<symbol_exprt> symbols;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    find_symbols(i_it->code, symbols);
    find_symbols(i_it->guard, symbols);
  }
  
  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it==goto_function.body.instructions.begin())
    {
      // first instruction, we instrument
    }
    else
    {
      goto_programt::const_targett previous=i_it;
      previous--;
      if(previous->is_goto() && !previous->guard.is_true())
      {
        // we follow a branch, instrument
      }
      else if(previous->is_function_call() && !previous->guard.is_true())
      {
        // we follow a function call, instrument
      }
      else if(i_it->is_target() || i_it->is_function_call())
      {
        // we are a target or a function call, instrument
      }
      else
        continue; // don't instrument
    }
  
    const interval_domaint &d=interval_analysis[i_it];

    exprt::operandst assertion;

    for(std::set<symbol_exprt>::const_iterator
        s_it=symbols.begin();
        s_it!=symbols.end();
        s_it++)
    {
      exprt tmp=d.make_expression(*s_it);
      if(!tmp.is_true())
        assertion.push_back(tmp);
    }
    
    if(!assertion.empty())
    {
      goto_programt::targett t=i_it;
      goto_function.body.insert_before_swap(i_it);
      t->make_assumption(conjunction(assertion));
      i_it++; // goes to original instruction
      t->source_location=i_it->source_location;
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
  
  interval_analysis(goto_functions);

  Forall_goto_functions(f_it, goto_functions)
    instrument_intervals(interval_analysis, f_it->second);
}
