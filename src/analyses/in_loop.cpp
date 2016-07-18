#include "in_loop.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool in_loopt::is_in_loop(goto_programt::const_targett loc)
{
  assert(location_set.find(loc)!=location_set.end());

  irep_idt id=loc->function;
  assert(!id.empty());

  fun_mapt::const_iterator it=fun_map.find(id);
  if(it!=fun_map.end())
  {
    const target_sett &target_set=it->second;
    target_sett::const_iterator t_it=target_set.find(loc);

    return t_it!=target_set.end();
  }
  else
  {
    // we need to compute loop information
    const goto_functiont &goto_function=goto_functions.function_map.at(id);
    assert(goto_function.body_available());
    const goto_programt &goto_program=goto_function.body;

    natural_loopst natural_loops;
    natural_loops(goto_program);

    target_sett &target_set=fun_map[id]; // new entry

    const natural_loopst::loop_mapt &loop_map=natural_loops.loop_map;

    for(natural_loopst::loop_mapt::const_iterator l_it=loop_map.begin();
        l_it!=loop_map.end(); l_it++)
    {
      const natural_loopst::natural_loopt &natural_loop=l_it->second;
      target_set.insert(natural_loop.begin(), natural_loop.end());
    }

    return is_in_loop(loc);
  }
}
