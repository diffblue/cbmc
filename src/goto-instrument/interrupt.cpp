/*******************************************************************\

Module: Interrupt Instrumentation

Author: Daniel Kroening, Lihao Liang

Date: June 2016

\*******************************************************************/

#ifdef DEBUG
#include <iostream>
#endif

#include <util/cprover_prefix.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/prefix.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_functions.h>

#include "interrupt.h"
#include "interrupt_util.h"

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

/*******************************************************************\

Function: interrupt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interrupt(
  value_setst &value_sets,
  const symbol_tablet &symbol_table,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont& goto_function,
#endif
  goto_programt &goto_program,
  const symbol_exprt &interrupt_handler,
  const rw_set_baset &isr_rw_set)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_function);
#endif
    rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
      , local_may
#endif
    );

    // potential race?
    bool race_on_read=potential_race_on_read(rw_set, isr_rw_set);
    bool race_on_write=potential_race_on_write(rw_set, isr_rw_set);

    if(!race_on_read && !race_on_write)
      continue;

    // Insert the call to the ISR.
    // We do before for races on Read, and before and after
    // for races on Write.

    if(race_on_read || race_on_write)
    {
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);

      const source_locationt &source_location=
        original_instruction.source_location;

      code_function_callt isr_call;
      isr_call.add_source_location()=source_location;
      isr_call.function()=interrupt_handler;

      goto_programt::targett t_goto=i_it;
      goto_programt::targett t_call=goto_program.insert_after(t_goto);
      goto_programt::targett t_orig=goto_program.insert_after(t_call);

      t_goto->make_goto(t_orig);
      t_goto->source_location=source_location;
      t_goto->guard=side_effect_expr_nondett(bool_typet());
      t_goto->function=original_instruction.function;

      t_call->make_function_call(isr_call);
      t_call->source_location=source_location;
      t_call->function=original_instruction.function;

      t_orig->swap(original_instruction);

      i_it=t_orig; // the for loop already counts us up
    }

    if(race_on_write)
    {
      // insert _after_ the instruction with race
      goto_programt::targett t_orig=i_it;
      t_orig++;

      goto_programt::targett t_goto=goto_program.insert_after(i_it);
      goto_programt::targett t_call=goto_program.insert_after(t_goto);

      const source_locationt &source_location=i_it->source_location;

      code_function_callt isr_call;
      isr_call.add_source_location()=source_location;
      isr_call.function()=interrupt_handler;

      t_goto->make_goto(t_orig);
      t_goto->source_location=source_location;
      t_goto->guard=side_effect_expr_nondett(bool_typet());
      t_goto->function=i_it->function;

      t_call->make_function_call(isr_call);
      t_call->source_location=source_location;
      t_call->function=i_it->function;

      i_it=t_call; // the for loop already counts us up
    }
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
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &interrupt_handler)
{
  // look up the ISR
  symbol_exprt isr=get_isr(symbol_table, interrupt_handler);

  // we first figure out which objects are read/written by the ISR
  const namespacet ns(symbol_table);
  rw_set_functiont isr_rw_set(
    value_sets, ns, goto_functions, isr);

  // now instrument

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=goto_functionst::entry_point() &&
       f_it->first!=isr.get_identifier())
      interrupt(
        value_sets, symbol_table,
#ifdef LOCAL_MAY
        f_it->second,
#endif
        f_it->second.body, isr, isr_rw_set);

  goto_functions.update();
}

/*******************************************************************\

Function: nested_interrupts

  Inputs:

 Outputs:

 Purpose: partial-order reduction for nested interrupts

\*******************************************************************/

void nested_interrupts(
  value_setst &value_sets,
  const symbol_tablet &symbol_table,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont& goto_function,
#endif
  goto_programt &goto_program,
  const irep_idt &function_id,
  const symbol_exprt &scheduling_function,
  const isr_rw_set_mapt &isr_rw_set_map)
{
  const namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {

#ifdef LOCAL_MAY
    local_may_aliast local_may(goto_function);
#endif
    rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
      , local_may
#endif
    );

    // potential race?
    bool race_on_read=false;
    bool race_on_write=false;

    for(const auto &it : isr_rw_set_map)
    {
      if(it.first==function_id)
        continue;

      const rw_set_function_rect &isr_rw_set=it.second;

      if(!race_on_read && potential_race_on_read(rw_set, isr_rw_set))
        race_on_read=true;
      if(!race_on_write && potential_race_on_write(rw_set, isr_rw_set))
        race_on_write=true;

      if (race_on_write)
        break;
    }

    if(race_on_read || race_on_write)
      insert_function_before_instruction(goto_program, i_it, scheduling_function);

    if(race_on_write)
      insert_function_after_instruction(goto_program, i_it, scheduling_function);
  }
}

/*******************************************************************\

Function: nested_interrupts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nested_interrupts(
  value_setst &value_sets,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &scheduling_function)
{
  // look up the scheduling function
  symbol_exprt sched_f=get_isr(symbol_table, scheduling_function);

  // look up all ISRs
  const namespacet ns(symbol_table);
  isr_mapt isr_map;
  build_isr_map(ns, isr_map);

  if(isr_map.size()<=0) {
    #ifdef DEBUG
    std::cout << "No interrupt handlers found" << std::endl;
    #endif
    return;
  }

  // figure out which objects are read/written by the ISR
  isr_rw_set_mapt isr_rw_set_map;

  for(const auto &isr_it : isr_map)
  {
    recursion_sett recursion_set;
    rw_set_function_rect isr_rw_set(
      value_sets, ns, goto_functions, isr_it.second, recursion_set);
    isr_rw_set_map.insert(
      std::pair<irep_idt, rw_set_function_rect>(isr_it.second, isr_rw_set));
  }

  // now instrument

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=goto_functionst::entry_point() &&
       f_it->first!=sched_f.get_identifier() &&
       f_it->first!=CPROVER_ENABLE_ISR &&
       f_it->first!=CPROVER_DISABLE_ISR)
      nested_interrupts(
        value_sets, symbol_table,
#ifdef LOCAL_MAY
        f_it->second,
#endif
        f_it->second.body, f_it->first, sched_f, isr_rw_set_map);

  goto_functions.update();
}
