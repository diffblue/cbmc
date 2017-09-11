/*******************************************************************\

Module: Slicer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer

#include "reachability_slicer.h"

#include <stack>

#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>
#include <goto-programs/cfg.h>

#include "full_slicer_class.h"
#include "reachability_slicer_class.h"

void reachability_slicert::fixedpoint_assertions(
  const is_threadedt &is_threaded,
  slicing_criteriont &criterion)
{
  queuet queue;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
    if(criterion(e_it->first) ||
       is_threaded(e_it->first))
      queue.push(e_it->second);

  while(!queue.empty())
  {
    cfgt::entryt e=queue.top();
    cfgt::nodet &node=cfg[e];
    queue.pop();

    if(node.reaches_assertion)
      continue;

    node.reaches_assertion=true;

    for(cfgt::edgest::const_iterator
        p_it=node.in.begin();
        p_it!=node.in.end();
        p_it++)
    {
      queue.push(p_it->first);
    }
  }
}

void reachability_slicert::slice(goto_functionst &goto_functions)
{
  // now replace those instructions that do not reach any assertions
  // by assume(false)

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available())
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const cfgt::nodet &e=cfg[cfg.entry_map[i_it]];
        if(!e.reaches_assertion &&
           !i_it->is_end_function())
          i_it->make_assumption(false_exprt());
      }

      // replace unreachable code by skip
      remove_unreachable(f_it->second.body);
    }

  // remove the skips
  remove_skip(goto_functions);
  goto_functions.update();
}

void reachability_slicer(goto_modelt &goto_model)
{
  reachability_slicert s;
  assert_criteriont a;
  s(goto_model.goto_functions, a);
}

void reachability_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &properties)
{
  reachability_slicert s;
  properties_criteriont p(properties);
  s(goto_model.goto_functions, p);
}
