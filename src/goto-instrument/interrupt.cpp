/*******************************************************************\

Module: Interrupt Instrumentation

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#include <cprover_prefix.h>
#include <std_expr.h>
#include <std_code.h>
#include <prefix.h>

#if 0
#include <hash_cont.h>
#include <expr_util.h>
#include <guard.h>

#include <goto-programs/remove_skip.h>
#endif

#include "interrupt.h"
#include "rw_set.h"

/*******************************************************************\

Function: interrupt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interrupt(
  value_setst &value_sets,
  const contextt &context,
  goto_programt &goto_program,
  const symbol_exprt &interrupt_handler)
{
  namespacet ns(context);
  
  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    rw_sett rw_set(ns, value_sets, i_it);
    
    if(rw_set.entries.empty()) continue;

    // insert the call to the ISR
    goto_programt::instructiont original_instruction;
    original_instruction.swap(instruction);
    const locationt &location=original_instruction.location;

    code_function_callt isr_call;
    isr_call.location()=location;
    isr_call.function()=interrupt_handler;

    goto_programt::targett t_goto=i_it;      
    goto_programt::targett t_call=goto_program.insert_after(t_goto);
    goto_programt::targett t_orig=goto_program.insert_after(t_call);

    t_goto->make_goto(t_orig);
    t_goto->location=location;
    t_goto->guard=side_effect_expr_nondett(bool_typet());

    t_call->make_function_call(isr_call);
    t_call->location=location;

    t_orig->swap(original_instruction);
    
    i_it=t_orig; // the for loop already counts us up
  }
}

/*******************************************************************\

Function: interrupt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interrupt(
  value_setst &value_sets,
  const contextt &context,
  goto_functionst &goto_functions,
  const irep_idt &interrupt_handler)
{
  // look up the ISR

  std::list<symbol_exprt> matches;

  forall_symbol_base_map(m_it, context.symbol_base_map, interrupt_handler)
  {
    // look it up
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(m_it->second);
    
    if(s_it==context.symbols.end()) continue;
  
    if(s_it->second.type.id()==ID_code)
      matches.push_back(s_it->second.symbol_expr());
  }
  
  if(matches.empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+"' not found";

  if(matches.size()>=2)
    throw "interrupt handler `"+id2string(interrupt_handler)+"' is ambiguous";

  symbol_exprt isr=matches.front();
  
  if(!to_code_type(isr.type()).arguments().empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+
          "' must not have arguments";

  // we first figure out which objects are read/written by the ISR

  // now instrument

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=ID_main &&
       f_it->first!=interrupt_handler)
      interrupt(value_sets, context, f_it->second.body, isr);

  goto_functions.update();
}

