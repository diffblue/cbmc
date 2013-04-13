/*******************************************************************\

Module: Slicer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include <util/i2string.h>

#include "reachability_slicer.h"
#include "remove_skip.h"
#include "remove_unreachable.h"
#include "cfg.h"
#include "reachability_slicer_class.h"

/*******************************************************************\

Function: reachability_slicert::fixedpoint_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicert::fixedpoint_assertions()
{
  queuet queue;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
    if(e_it->first->is_assert() ||
       e_it->second.threaded)
      queue.push(&e_it->second);

  while(!queue.empty())
  {
    cfgt::iterator e=queue.top();
    queue.pop();

    if(e->reaches_assertion) continue;

    e->reaches_assertion=true;
    
    for(cfgt::entriest::const_iterator
        p_it=e->predecessors.begin();
        p_it!=e->predecessors.end();
        p_it++)
    {
      queue.push(*p_it);
    }
  }
}

/*******************************************************************\

Function: reachability_slicert::fixedpoint_threads

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicert::fixedpoint_threads()
{
  queuet queue;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
    if(e_it->first->is_start_thread())
      queue.push(&e_it->second);

  while(!queue.empty())
  {
    cfgt::iterator e=queue.top();
    queue.pop();

    if(e->threaded) continue;

    e->threaded=true;
    
    for(cfgt::entriest::const_iterator
        p_it=e->successors.begin();
        p_it!=e->successors.end();
        p_it++)
    {
      queue.push(*p_it);
    }
  }
}

/*******************************************************************\

Function: reachability_slicert::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicert::slice(goto_functionst &goto_functions)
{
  // now replace those instructions that do not reach any assertions
  // by self-loops

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available)
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const cfgt::entryt &e=cfg.entry_map[i_it];
        if(!e.reaches_assertion &&
           !i_it->is_end_function())
          i_it->make_goto(i_it);
      }

      // replace unreachable code by skip
      remove_unreachable(f_it->second.body);
    }
  
  // remove the skips
  remove_skip(goto_functions);
  goto_functions.update();
}

/*******************************************************************\

Function: reachability_slicert::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicert::slice(goto_programt &goto_program)
{
  // now replace those instructions that do not reach any assertions
  // by assume(false)

  Forall_goto_program_instructions(it, goto_program)
  {
    const cfgt::entryt &e=cfg.entry_map[it];
    if(!e.reaches_assertion)
      it->make_assumption(false_exprt());
  }
  
  // replace unreachable code by skip
  remove_unreachable(goto_program);
  
  // remove the skips
  remove_skip(goto_program);
  goto_program.update();
}

/*******************************************************************\

Function: reachability_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicer(goto_programt &goto_program)
{
  reachability_slicert()(goto_program);
}

/*******************************************************************\

Function: reachability_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reachability_slicer(goto_functionst &goto_functions)
{
  reachability_slicert()(goto_functions);
}
