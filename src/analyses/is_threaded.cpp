/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#include "ai.h"
#include "is_threaded.h"

class is_threaded_domaint:public ai_domain_baset
{
  bool has_spawn;
public:
  bool is_threaded;
  
  inline is_threaded_domaint():has_spawn(false), is_threaded(false)
  {
  }

  inline bool merge(
    const is_threaded_domaint &src,
    locationt from,
    locationt to)
  {
    bool old_h_s=has_spawn;
    if(src.has_spawn &&
       (from->is_end_function() ||
        from->function==to->function))
      has_spawn=true;

    bool old_i_t=is_threaded;
    if(has_spawn ||
       (src.is_threaded &&
       !from->is_end_function()))
      is_threaded=true;

    return old_i_t!=is_threaded || old_h_s!=has_spawn;
  }
  
  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns)
  {
    if(from->is_start_thread() ||
       to->is_end_thread())
    {
      has_spawn=true;
      is_threaded=true;
    }
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
  // the analysis doesn't actually use the namespace, fake one
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  ait<is_threaded_domaint> is_threaded_analysis;
  
  is_threaded_analysis(goto_functions, ns);
  
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

