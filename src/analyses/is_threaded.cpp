/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#include "static_analysis.h"
#include "is_threaded.h"

class is_threaded_domaint:public domain_baset
{
public:
  bool is_threaded;
  
  inline is_threaded_domaint():is_threaded(false)
  {
  }

  inline bool merge(const is_threaded_domaint &other)
  {
    bool old=is_threaded;
    is_threaded=is_threaded || other.is_threaded;
    return old!=is_threaded;
  }
  
  void transform(
    const namespacet &ns,
    locationt from,
    locationt to)
  {
    if(from->is_start_thread())
      is_threaded=true;
  }
};

/*******************************************************************\

Function: is_threadedt::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void is_threadedt::compute(const goto_functionst &goto_functions)
{
  static_analysist<is_threaded_domaint> is_threaded_analysis(ns);
  
  is_threaded_analysis(goto_functions);
  
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    const goto_programt &goto_program=f_it->second.body;
    for(goto_programt::instructionst::const_iterator
        i_it=goto_program.instructions.begin();
        i_it!=goto_program.instructions.end();
        i_it++)
      if(is_threaded_analysis[i_it].is_threaded)
        is_threaded_set.insert(i_it);
  }
}

