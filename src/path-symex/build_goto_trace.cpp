/*******************************************************************\

Module: Build Goto Trace from State History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "build_goto_trace.h"

/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose: follow state history to build a goto trace

\*******************************************************************/

void build_goto_trace(
  const path_symex_statet &state,
  const decision_proceduret &decision_procedure,
  goto_tracet &goto_trace)
{
  // follow the history in the state,
  // but in a forwards-fashion
  
  std::vector<path_symex_step_reft> steps;
  state.history.build_history(steps);
  
  unsigned step_nr;
  
  for(step_nr=0; step_nr<steps.size(); step_nr++)
  {
    const path_symex_stept &step=*steps[step_nr];
  
    goto_trace_stept trace_step;
    
    assert(!step.pc.is_nil());
    trace_step.pc=state.locs[step.pc].target;
    trace_step.thread_nr=step.thread_nr;
    trace_step.step_nr=step_nr;
    
    const goto_programt::instructiont &instruction=*trace_step.pc;
    
    switch(instruction.type)
    {
    case ASSIGN:
      trace_step.type=goto_trace_stept::ASSIGNMENT;
      trace_step.full_lhs=step.full_lhs;
      trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      break;
    
    case DECL:
      trace_step.type=goto_trace_stept::DECL;
      trace_step.full_lhs=step.full_lhs;
      trace_step.lhs_object=to_symbol_expr(step.full_lhs);
      trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      break;
      
    case DEAD:
      trace_step.type=goto_trace_stept::DEAD;
      break;
      
    case ASSUME:
      trace_step.type=goto_trace_stept::ASSUME;
      break;
      
    case FUNCTION_CALL:
      trace_step.type=goto_trace_stept::FUNCTION_CALL;
      break;
    
    case END_FUNCTION:
      trace_step.type=goto_trace_stept::FUNCTION_RETURN;
      break;
      
    case START_THREAD:
      trace_step.type=goto_trace_stept::SPAWN;
      break;
    
    case ATOMIC_BEGIN:
      trace_step.type=goto_trace_stept::ATOMIC_BEGIN;
      break;
    
    case ATOMIC_END:
      trace_step.type=goto_trace_stept::ATOMIC_END;
      break;
    
    default:
      trace_step.type=goto_trace_stept::LOCATION;
    }
  
    goto_trace.add_step(trace_step);
  }

  // add assertion
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  assert(instruction.is_assert());
  
  {
    goto_trace_stept trace_step;

    trace_step.pc=state.get_instruction();
    trace_step.thread_nr=state.get_current_thread();
    trace_step.step_nr=step_nr;
    trace_step.type=goto_trace_stept::ASSERT;

    const irep_idt &comment=
      instruction.source_location.get_comment();

    if(comment!=irep_idt())
      trace_step.comment=id2string(comment);
    else
      trace_step.comment="assertion";

    goto_trace.add_step(trace_step);  
  }
}
