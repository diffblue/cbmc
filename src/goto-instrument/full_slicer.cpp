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

  // fill queue with asserts
  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
    if(e_it->first->is_assert())
    {
      get_objects(e_it->first->guard, e_it->second.required_objects);
      queue.push(&e_it->second);
    }

  // process queue until empty
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
  const object_id_sett &old_set=e->required_objects;
  object_id_sett new_set=e->required_objects; // copy!
  
  const goto_programt::instructiont &instruction=*(e->PC);

  switch(instruction.type)
  {
  // these introduce control-flow dependencies
  case ASSUME:
    {
      object_id_sett w;
      get_objects(instruction.guard, w);
      
      bool found=false;

      // does it constrain something we need?
      for(object_id_sett::const_iterator
          o_it1=w.begin(); o_it1!=w.end(); o_it1++)
        if(old_set.find(*o_it1)!=old_set.end())
          found=true;

      if(found)
      {
        e->node_required=true;
        new_set.insert(w.begin(), w.end());
      }
    }    
    break;
    
  // these introduce control-flow dependencies
  case GOTO:
    {
      object_id_sett w;
      get_objects(instruction.guard, w);
      
      bool found=false;

      // does it constrain something we need?
      for(object_id_sett::const_iterator
          o_it1=w.begin(); o_it1!=w.end(); o_it1++)
        if(old_set.find(*o_it1)!=old_set.end())
          found=true;

      if(found)
      {
        e->node_required=true;
        new_set.insert(w.begin(), w.end());
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
        object_id_sett::iterator o_it2=old_set.find(*o_it1);
        if(o_it2!=old_set.end())
        {
          found=true;
          // remove what is written
          new_set.erase(o_it2);
        }
      }

      if(found)
      {
        e->node_required=true;
        // add what it reads
        get_objects_r(code_assign, new_set);
      }
    }    
    break;
  
  case DECL: // this cuts off dependencies
    {
      object_idt object_id(to_symbol_expr(instruction.code.op0()));
      if(old_set.find(object_id)!=old_set.end())
      {
        e->node_required=true;
        new_set.erase(object_id);
      }
    }
    break;
  
  case FUNCTION_CALL:
    {
      // These are like assignments for the arguments.
      // The LHS is dealt with on return.
      const code_function_callt &code_function_call=
        to_code_function_call(instruction.code);

      assert(code_function_call.function().type().id()==ID_code);
      
      const code_typet &code_type=
        to_code_type(code_function_call.function().type());

      assert(code_function_call.arguments().size()>=
             code_type.arguments().size());

      for(unsigned i=0; i<code_type.arguments().size(); i++)
      {
        object_idt lhs_id=object_idt(code_type.arguments()[i].get_identifier());

        if(old_set.find(lhs_id)!=old_set.end())
        {
          new_set.erase(lhs_id);
          e->node_required=true;
          get_objects(code_function_call.arguments()[i], new_set);
        }
      }
    }    
    break;
  
  default:;
  }
  
  return new_set;
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
