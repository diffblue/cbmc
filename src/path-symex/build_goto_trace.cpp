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
  const locst &locs,
  const statet &state,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  // follow the history in the state
  
  unsigned step_nr=0;

  for(statet::historyt::const_iterator
      h_it=state.history.begin();
      h_it!=state.history.end();
      h_it++, step_nr++)
  {
    const statet::stept &step=*h_it;
  
    goto_trace_stept trace_step;

    trace_step.pc=locs[step.pc()].target;
    trace_step.thread_nr=step.thread_nr;
    trace_step.step_nr=step_nr;
    
    const goto_programt::instructiont &instruction=*trace_step.pc;
    
    switch(instruction.type)
    {
    case ASSIGN:
      trace_step.type=goto_trace_stept::ASSIGNMENT;
      trace_step.full_lhs=step.lhs;
      trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      break;
    
    case DECL:
      trace_step.type=goto_trace_stept::DECL;
      trace_step.full_lhs=step.lhs;
      trace_step.lhs_object=to_symbol_expr(step.lhs);
      trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      break;
      
    case ASSUME:
      trace_step.type=goto_trace_stept::ASSUME;
      break;
    
    case ASSERT:
      // only add last one as ASSERT

      if(h_it==--state.history.end())
      {
        trace_step.type=goto_trace_stept::ASSERT;

        const irep_idt &comment=instruction.location.get_comment();
        if(comment!=irep_idt())
          trace_step.comment=id2string(comment);
        else
          trace_step.comment="assertion";
      }
      else
        trace_step.type=goto_trace_stept::LOCATION;
        
      break;
    
    default:
      trace_step.type=goto_trace_stept::LOCATION;
    }
  
    goto_trace.add_step(trace_step);
  }
}
