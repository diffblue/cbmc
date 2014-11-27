/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening, Vincent Nimal

Date: September 2011

\*******************************************************************/

/*
 * Strategy: we first overapproximate all the read/write sequences of
 * the program executions with a read/write graph. We then detect the
 * pairs potentially dangerous, and to be delayed in some executions
 * of the program. We finally insert the corresponding instrumentations
 * in the program.
 */

#include <set>

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/i2string.h>
#include <util/message.h>

#include <goto-programs/remove_skip.h>

#include "../rw_set.h"

#include "weak_memory.h"
#include "shared_buffers.h"
#include "goto2graph.h"

/*******************************************************************\

Function: introduce_temporaries

  Inputs:

 Outputs:

 Purpose: all access to shared variables is pushed into assignments

\*******************************************************************/

void introduce_temporaries(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  const irep_idt &function,
  goto_programt &goto_program,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  messaget& message)
{
  namespacet ns(symbol_table);
  unsigned tmp_counter=0;

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_function);
#endif
	
  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    message.debug() <<instruction.source_location<< messaget::eom;

    if(instruction.is_goto() ||
       instruction.is_assert() ||
       instruction.is_assume())
    {
      rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
      , local_may
#endif
      );
      if(rw_set.empty()) continue;
      
      symbolt new_symbol;
      new_symbol.base_name="$tmp_guard";
      new_symbol.name=id2string(function)+"$tmp_guard"+i2string(tmp_counter++);
      new_symbol.type=bool_typet();
      new_symbol.is_static_lifetime=true;
      new_symbol.is_thread_local=true;
      new_symbol.value.make_nil();
      
      symbol_exprt symbol_expr=new_symbol.symbol_expr();
      
      symbolt *symbol_ptr;
      symbol_table.move(new_symbol, symbol_ptr);
      
      goto_programt::instructiont new_i;
      new_i.make_assignment();
      new_i.code=code_assignt(symbol_expr, instruction.guard);
      new_i.source_location=instruction.source_location;
      new_i.function=instruction.function;

      // replace guard
      instruction.guard=symbol_expr;
      goto_program.insert_before_swap(i_it, new_i);

      i_it++; // step forward
    }
    else if(instruction.is_function_call())
    {
      // nothing
    }
  }
}

/*******************************************************************\

Function: weak_memory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory(
  memory_modelt model,
  value_setst& value_sets,
  symbol_tablet& symbol_table,
  goto_functionst &goto_functions,
  bool SCC,
  instrumentation_strategyt event_strategy,
  unsigned unwinding_bound,
  bool no_cfg_kill,
  bool no_dependencies,
  loop_strategyt duplicate_body,
  unsigned input_max_var,
  unsigned input_max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option,
  bool hide_internals, 
  message_handlert& message_handler,
  bool ignore_arrays)
{
  messaget message(message_handler);

  // no more used -- dereferences performed in rw_set
  // get rid of pointers
  // remove_pointers(goto_functions, symbol_table, value_sets);
  // add_failed_symbols(symbol_table);
  // message.status() <<"pointers removed"<< messaget::eom;

  message.status() << "--------" << messaget::eom;

  // all access to shared variables is pushed into assignments
  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
      f_it->first!=goto_functionst::entry_point())
      introduce_temporaries(value_sets, symbol_table, f_it->first, 
        f_it->second.body, 
#ifdef LOCAL_MAY
        f_it->second,
#endif
        message);

  message.status() << "Temp added" << messaget::eom;

  unsigned max_thds = 0;
  instrumentert instrumenter(symbol_table, goto_functions, message);
  max_thds=instrumenter.goto2graph_cfg(value_sets, model, no_dependencies, 
    duplicate_body);
  message.status()<<"abstraction completed"<<messaget::eom;

  // collects cycles, directly or by SCCs
  if(input_max_var!=0 || input_max_po_trans!=0)
    instrumenter.set_parameters_collection(input_max_var,
      input_max_po_trans, ignore_arrays);
  else
    instrumenter.set_parameters_collection(max_thds, ignore_arrays);
  
  if(SCC)
  {
    instrumenter.collect_cycles_by_SCCs(model);
    message.status()<<"cycles collected: "<<messaget::eom;
    unsigned interesting_scc = 0;
    unsigned total_cycles = 0;
    for(unsigned i=0; i<instrumenter.num_sccs; i++)
      if(instrumenter.egraph_SCCs[i].size()>=4)
      {
        message.status()<<"SCC #"<<i<<": "
          <<instrumenter.set_of_cycles_per_SCC[interesting_scc++].size()
          <<" cycles found"<<messaget::eom;
        total_cycles += instrumenter
          .set_of_cycles_per_SCC[interesting_scc++].size();
      }

    /* if no cycle, no need to instrument */
    if(total_cycles == 0)
    {
      message.status()<<"program safe -- no need to instrument"<<messaget::eom;
      return;
    }
  }
  else
  {
    instrumenter.collect_cycles(model);
    message.status()<<"cycles collected: "<<instrumenter.set_of_cycles.size()
      <<" cycles found"<<messaget::eom;

    /* if no cycle, no need to instrument */
    if(instrumenter.set_of_cycles.size() == 0)
    {
      message.status()<<"program safe -- no need to instrument"<<messaget::eom;
      return;
    }
  }

  if(!no_cfg_kill)
    instrumenter.cfg_cycles_filter();

  // collects instructions to instrument, depending on the strategy selected
  if(event_strategy == my_events)
  {
    const std::set<unsigned> events_set = instrumentert::extract_my_events();
    instrumenter.instrument_my_events(events_set);
  }  
  else
    instrumenter.instrument_with_strategy(event_strategy);

  // prints outputs
  instrumenter.set_rendering_options(render_po, render_file, render_function);
  instrumenter.print_outputs(model, hide_internals);

  // now adds buffers
  shared_bufferst shared_buffers(symbol_table, max_thds, message);

  if(cav11_option)
    shared_buffers.set_cav11(model);

  // stores the events to instrument
  shared_buffers.cycles = instrumenter.var_to_instr; // var in the cycles
  shared_buffers.cycles_loc = instrumenter.id2loc; // instrumented places
  shared_buffers.cycles_r_loc = instrumenter.id2cycloc; // places in the cycles

  // for reads delays
  shared_buffers.affected_by_delay(symbol_table,value_sets,goto_functions);

  for(std::set<irep_idt>::iterator it=
    shared_buffers.affected_by_delay_set.begin(); 
    it!=shared_buffers.affected_by_delay_set.end();
    it++)
    message.debug()<<id2string(*it)<<messaget::eom;

  message.status()<<"I instrument:"<<messaget::eom;
  for(std::set<irep_idt>::iterator it=shared_buffers.cycles.begin(); 
    it!=shared_buffers.cycles.end(); it++)
  {
    typedef std::multimap<irep_idt,source_locationt>::iterator m_itt;
    const std::pair<m_itt,m_itt> ran=
      shared_buffers.cycles_loc.equal_range(*it);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      message.result() << ((*it)==""?"fence":*it)<<", "<<ran_it->second<<messaget::eom;
  }

  shared_bufferst::cfg_visitort visitor(shared_buffers, symbol_table, 
    goto_functions);
  visitor.weak_memory(value_sets, goto_functions.entry_point(), model);

  /* removes potential skips */
  Forall_goto_functions(f_it, goto_functions)
    remove_skip(f_it->second.body);

  // initialization code for buffers
  shared_buffers.add_initialization_code(goto_functions);
  
  // update counters etc.
  goto_functions.update();

  message.status()<< "Goto-program instrumented" << messaget::eom;
}
