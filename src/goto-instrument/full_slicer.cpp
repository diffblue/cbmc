/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/remove_skip.h>

#include "full_slicer.h"
#include "full_slicer_class.h"
#include "object_id.h"

/*******************************************************************\

Function: full_slicert::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::fixedpoint()
{
  queuet queue;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
    if(e_it->first->is_assert())
    {
      get_objects(e_it->first->guard, e_it->second.required_objects);
      queue.push(&e_it->second);
    }

  while(!queue.empty())
  {
    cfgt::iterator e=queue.top();
    queue.pop();
    
    // look at required_objects
    object_id_sett required_objects=transform(e);

    for(cfgt::entriest::const_iterator
        p_it=e->predecessors.begin();
        p_it!=e->predecessors.end();
        p_it++)
    {
      (*p_it)->required_objects.insert(
        required_objects.begin(), required_objects.end());

      queue.push(*p_it);
    }
  }
}

/*******************************************************************\

Function: full_slicert::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::slice(goto_functionst &goto_functions)
{
  // build the CFG data structure
  cfg(goto_functions);
  
  // compute the fixedpoint
  fixedpoint();

  // now replace those instructions that are not needed
  // by skips

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available)
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const cfgt::entryt &e=cfg.entry_map[i_it];
        if(!e.node_required &&
           !i_it->is_end_function())
          i_it->make_skip();
      }
    }
  
  // remove the skips
  remove_skip(goto_functions);
  goto_functions.update();
}

/*******************************************************************\

Function: full_slicert::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

object_id_sett full_slicert::transform(cfgt::iterator e)
{
  object_id_sett result=e->required_objects;
  
  const goto_programt::instructiont &instruction=*(e->PC);

  switch(instruction.type)
  {
  // these introduce control-flow dependencies
  case ASSUME:
    {
      object_id_sett w;
      get_objects(instruction.guard, w);
      
      bool found=false;

      // does it write something we need?
      for(object_id_sett::const_iterator
          o_it1=w.begin(); o_it1!=w.end(); o_it1++)
        if(result.find(*o_it1)!=result.end())
          found=true;

      if(found)
      {
        e->node_required=true;
        result.insert(w.begin(), w.end());
      }
    }    
    break;
  
  case OTHER:
    break;

  case RETURN:
    // TODO
    break;
    
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      
      object_id_sett w;
      get_objects_w(code_assign, w);
      
      bool found=false;

      // does it write something we need?
      for(object_id_sett::const_iterator
          o_it1=w.begin(); o_it1!=w.end(); o_it1++)
      {
        object_id_sett::iterator o_it2=result.find(*o_it1);
        if(o_it2!=result.end())
        {
          found=true;
          // remove what is written
          result.erase(o_it2);
        }
      }

      if(found)
      {
        e->node_required=true;
        // add what it reads
        get_objects_r(code_assign, result);
      }
    }    
    break;
  
  case DECL: // this cuts off dependencies
    {
      object_idt object_id(to_symbol_expr(instruction.code.op0()));
      if(result.find(object_id)!=result.end())
      {
        e->node_required=true;
        result.erase(object_id);
      }
    }
    break;
  
  case FUNCTION_CALL:
    {
      #if 0      
      // these are like assignments for the arguments
      // and for the LHS
      const code_function_callt &code_function_call=
        to_code_function_call(instruction.code);

      object_id_sett w;
      get_objects_w(code_function_call, w);
      
      bool found=false;

      // does it write something we need?
      for(object_id_sett::const_iterator
          o_it1=w.begin(); o_it1!=w.end(); o_it1++)
      {
        object_id_sett::iterator o_it2=result.find(*o_it1);
        if(o_it2!=result.end())
        {
          found=true;
          // remove what is written
          result.erase(o_it2);
        }
      }

      if(found)
      {
        e->node_required=true;
        // add what it reads
        get_objects_r(code_assign, result);
      }
      #endif
    }    
    break;
  
  default:;
  }
  
  return result;
}

/*******************************************************************\

Function: slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicer(goto_functionst &goto_functions)
{
  full_slicert()(goto_functions);
}
