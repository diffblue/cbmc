/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#include <cprover_prefix.h>

#if 0
#include <hash_cont.h>
#include <std_expr.h>
#include <expr_util.h>
#include <guard.h>
#include <prefix.h>

#include <goto-programs/remove_skip.h>
#endif

#include "interrupt.h"
#include "rw_set.h"

/*******************************************************************\

Function: mmio

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void mmio(
  value_setst &value_sets,
  const contextt &context,
  goto_programt &goto_program)
{
  namespacet ns(context);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      rw_set_loct rw_set(ns, value_sets, i_it);
      
      if(rw_set.empty()) continue;
  
      #if 0    
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const locationt &location=original_instruction.location;
      
      instruction.make_atomic_begin();
      instruction.location=location;
      i_it++;
      
      // we first perform (non-deterministically) up to 2 writes for
      // stuff that is potentially read
      forall_rw_set_entries(e_it, rw_set)
        if(e_it->second.r)
        {
          const shared_bufferst::varst &vars=shared_buffers(e_it->second.object);
          irep_idt choice0=shared_buffers.choice("0");
          irep_idt choice1=shared_buffers.choice("1");
          
          symbol_exprt choice0_expr=symbol_exprt(choice0, bool_typet());
          symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());
        
          symbol_exprt w_buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
          symbol_exprt w_buff1_expr=symbol_exprt(vars.w_buff1, vars.type);
          
          symbol_exprt w_used0_expr=symbol_exprt(vars.w_used0, bool_typet());
          symbol_exprt w_used1_expr=symbol_exprt(vars.w_used1, bool_typet());
          
          exprt nondet_bool_expr=side_effect_nondet_exprt(bool_typet());
          
          exprt choice0_rhs=and_exprt(nondet_bool_expr, w_used0_expr);
          exprt choice1_rhs=and_exprt(nondet_bool_expr, w_used1_expr);
          
          // throw 2 Boolean dice
          shared_buffers.assignment(goto_program, i_it, location, choice0, choice0_rhs);
          shared_buffers.assignment(goto_program, i_it, location, choice1, choice1_rhs);
          
          exprt lhs=symbol_exprt(e_it->second.object, vars.type);
          
          exprt value=
            if_exprt(choice0_expr, w_buff0_expr,
              if_exprt(choice1_expr, w_buff1_expr, lhs));

          // write one of the buffer entries
          shared_buffers.assignment(goto_program, i_it, location, e_it->second.object, value);
          
          // update 'used' flags
          exprt w_used0_rhs=if_exprt(choice0_expr, false_exprt(), w_used0_expr);
          exprt w_used1_rhs=and_exprt(if_exprt(choice1_expr, false_exprt(), w_used1_expr), w_used0_expr);

          shared_buffers.assignment(goto_program, i_it, location, vars.w_used0, w_used0_rhs);
          shared_buffers.assignment(goto_program, i_it, location, vars.w_used1, w_used1_rhs);
        }

      // now rotate the write buffers for anything that is written
      forall_rw_set_entries(e_it, rw_set)
        if(e_it->second.w)
        {
          const shared_bufferst::varst &vars=shared_buffers(e_it->second.object);
        
          // w_used1=w_used0; w_used0=true;
          shared_buffers.assignment(goto_program, i_it, location, vars.w_used1, vars.w_used0);
          shared_buffers.assignment(goto_program, i_it, location, vars.w_used0, true_exprt());

          // w_buff1=w_buff0; w_buff0=RHS;
          shared_buffers.assignment(goto_program, i_it, location, vars.w_buff1, vars.w_buff0);
          shared_buffers.assignment(goto_program, i_it, location, vars.w_buff0, original_instruction.code.op1());
        }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->location=location;
      i_it++;
        
      i_it--; // the for loop already counts us up
      #endif
    }
  }
}

/*******************************************************************\

Function: mmio

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void mmio(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions)
{
  // we first figure out which objects are read/written by the ISR



  // now instrument

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=ID_main)
      mmio(value_sets, context, f_it->second.body);

  goto_functions.update();
}

