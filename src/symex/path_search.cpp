/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/time_stopping.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <path-symex/path_symex.h>
#include <path-symex/build_goto_trace.h>

#include "path_search.h"

/*******************************************************************\

Function: path_searcht::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_searcht::resultt path_searcht::operator()(
  const goto_functionst &goto_functions)
{
  locst locs(ns);
  var_mapt var_map(ns);
  
  locs.build(goto_functions);

  // this is the container for the history-forest  
  path_symex_historyt history;
  
  queue.push_back(initial_state(var_map, locs, history));
  
  // set up the statistics
  number_of_dropped_states=0;
  number_of_paths=0;
  number_of_VCCs=0;
  number_of_steps=0;
  number_of_VCCs_after_simplification=0;
  number_of_failed_properties=0;

  // stop the time
  start_time=current_time();
  
  initialize_property_map(goto_functions);
  
  while(!queue.empty())
  {
    number_of_steps++;
  
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();
    
    if(drop_state(*state))
    {
      number_of_dropped_states++;
      number_of_paths++;
      queue.erase(state);
      continue;
    }
    
    if(!state->is_executable())
    {
      number_of_paths++;
      queue.erase(state);
      continue;
    }
    
    if(number_of_steps%1000==0)
    {
      status() << "Queue " << queue.size()
               << " thread " << state->get_current_thread()
               << "/" << state->threads.size()
               << " PC " << state->pc() << messaget::eom;
    }

    // an error, possibly?
    if(state->get_instruction()->is_assert())
    {
      if(show_vcc)
        do_show_vcc(*state, ns);
      else
      {
        check_assertion(*state, ns);
        
        // all assertions failed?
        if(number_of_failed_properties==property_map.size())
          break;
      }
    }
    
    // execute
    path_symex(*state, queue);
  }
  
  report_statistics();
  
  return number_of_failed_properties==0?SAFE:UNSAFE;
}

/*******************************************************************\

Function: path_searcht::report_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::report_statistics()
{
  // report a bit
  status() << "Number of dropped states: "
           << number_of_dropped_states << messaget::eom;

  status() << "Number of paths: "
           << number_of_paths << messaget::eom;

  status() << "Generated " << number_of_VCCs << " VCC(s), "
           << number_of_VCCs_after_simplification
           << " remaining after simplification"
           << messaget::eom;
  
  time_periodt total_time=current_time()-start_time;
  status() << "Runtime: " << total_time << "s total, "
           << sat_time << "s SAT" << messaget::eom;
}

/*******************************************************************\

Function: path_searcht::pick_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_searcht::queuet::iterator path_searcht::pick_state()
{
  // Picking the first one is a DFS.
  return queue.begin();
}

/*******************************************************************\

Function: path_searcht::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::do_show_vcc(
  statet &state,
  const namespacet &ns)
{
  // keep statistics
  number_of_VCCs++;
  
  const goto_programt::instructiont &instruction=
    *state.get_instruction();
    
  mstreamt &out=result();

  if(instruction.source_location.is_not_nil())
    out << instruction.source_location << "\n";
  
  if(instruction.source_location.get_comment()!="")
    out << instruction.source_location.get_comment() << "\n";
    
  unsigned count=1;
  
  std::vector<path_symex_step_reft> steps;
  state.history.build_history(steps);

  for(std::vector<path_symex_step_reft>::const_iterator
      s_it=steps.begin();
      s_it!=steps.end();
      s_it++)
  {      
    if((*s_it)->guard.is_not_nil())
    {
      std::string string_value=from_expr(ns, "", (*s_it)->guard);
      out << "{-" << count << "} " << string_value << "\n";
      count++;
    }

    if((*s_it)->ssa_rhs.is_not_nil())
    {
      equal_exprt equality((*s_it)->ssa_lhs, (*s_it)->ssa_rhs);
      std::string string_value=from_expr(ns, "", equality);
      out << "{-" << count << "} " << string_value << "\n";
      count++;
    }
  }

  out << "|--------------------------" << "\n";
  
  exprt assertion=state.read(instruction.guard);

  out << "{" << 1 << "} "
      << from_expr(ns, "", assertion) << "\n";

  if(!assertion.is_true())
    number_of_VCCs_after_simplification++;
  
  out << eom;
}

/*******************************************************************\

Function: path_searcht::drop_state

  Inputs:

 Outputs:

 Purpose: decide whether to drop a state

\*******************************************************************/

bool path_searcht::drop_state(const statet &state) const
{
  // depth limit
  if(depth_limit_set && state.get_depth()>depth_limit) return true;
  
  // context bound
  if(context_bound_set && state.get_no_thread_interleavings()) return true;
  
  // unwinding limit -- loops
  if(unwind_limit_set && state.get_instruction()->is_backwards_goto())
  {
    for(path_symex_statet::unwinding_mapt::const_iterator
        it=state.unwinding_map.begin();
        it!=state.unwinding_map.end();
        it++)
      if(it->second>unwind_limit)
        return true;
  }
  
  // unwinding limit -- recursion
  if(unwind_limit_set && state.get_instruction()->is_function_call())
  {
    for(path_symex_statet::recursion_mapt::const_iterator
        it=state.recursion_map.begin();
        it!=state.recursion_map.end();
        it++)
      if(it->second>unwind_limit)
        return true;
  }
  
  return false;
}

/*******************************************************************\

Function: path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::check_assertion(
  statet &state,
  const namespacet &ns)
{
  // keep statistics
  number_of_VCCs++;
  
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  irep_idt property_name=instruction.source_location.get_property_id();
  property_entryt &property_entry=property_map[property_name];
  
  if(property_entry.status==FAIL)
    return; // already failed
  else if(property_entry.status==NOT_REACHED)
    property_entry.status=PASS; // well, for now!

  // the assertion in SSA
  exprt assertion=
    state.read(instruction.guard);

  if(assertion.is_true()) return; // no error, trivially

  // keep statistics
  number_of_VCCs_after_simplification++;
  
  status() << "Checking property " << property_name << eom;

  // take the time
  absolute_timet sat_start_time=current_time();

  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);
  
  satcheck.set_message_handler(get_message_handler());
  bv_pointers.set_message_handler(get_message_handler());

  if(!state.check_assertion(bv_pointers))
  {
    build_goto_trace(state, bv_pointers, property_entry.error_trace);
    property_entry.status=FAIL;
    number_of_failed_properties++;
  }
  
  sat_time+=current_time()-sat_start_time;
}

/*******************************************************************\

Function: path_searcht::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::initialize_property_map(
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
    {
      const goto_programt &goto_program=it->second.body;
    
      for(goto_programt::instructionst::const_iterator
          it=goto_program.instructions.begin();
          it!=goto_program.instructions.end();
          it++)
      {
        if(!it->is_assert())
          continue;
      
        const source_locationt &source_location=it->source_location;
      
        irep_idt property_name=source_location.get_property_id();
        
        property_entryt &property_entry=property_map[property_name];
        property_entry.status=NOT_REACHED;
        property_entry.description=source_location.get_comment();
      }
    }    
}
