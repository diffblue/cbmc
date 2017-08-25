/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Path-based Symbolic Execution

#include "path_search.h"

#include <util/simplify_expr.h>
#include <util/time_stopping.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <path-symex/path_symex.h>
#include <path-symex/build_goto_trace.h>

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
  number_of_feasible_paths=0;
  number_of_infeasible_paths=0;
  number_of_VCCs_after_simplification=0;
  number_of_failed_properties=0;
  number_of_locs=locs.size();

  // stop the time
  start_time=current_time();

  initialize_property_map(goto_functions);

  while(!queue.empty())
  {
    number_of_steps++;

    // Pick a state from the queue,
    // according to some heuristic.
    // The state moves to the head of the queue.
    pick_state();

    // move into temporary queue
    queuet tmp_queue;
    tmp_queue.splice(
      tmp_queue.begin(), queue, queue.begin(), ++queue.begin());

    try
    {
      statet &state=tmp_queue.front();

      // record we have seen it
      loc_data[state.pc().loc_number].visited=true;

      debug() << "Loc: #" << state.pc().loc_number
              << ", queue: " << queue.size()
              << ", depth: " << state.get_depth();
      for(const auto &s : queue)
        debug() << ' ' << s.get_depth();

      debug() << eom;

      if(drop_state(state))
      {
        number_of_dropped_states++;
        number_of_paths++;
        continue;
      }

      if(!state.is_executable())
      {
        number_of_paths++;
        continue;
      }

      if(eager_infeasibility &&
         state.last_was_branch() &&
         !is_feasible(state))
      {
        number_of_infeasible_paths++;
        number_of_paths++;
        continue;
      }

      if(number_of_steps%1000==0)
      {
        time_periodt running_time=current_time()-start_time;
        status() << "Queue " << queue.size()
                 << " thread " << state.get_current_thread()+1
                 << '/' << state.threads.size()
                 << " PC " << state.pc()
                 << " [" << number_of_steps << " steps, "
                 << running_time << "s]" << messaget::eom;
      }

      // an error, possibly?
      if(state.get_instruction()->is_assert())
      {
        if(show_vcc)
          do_show_vcc(state);
        else
        {
          check_assertion(state);

          // all assertions failed?
          if(number_of_failed_properties==property_map.size())
            break;
        }
      }

      // execute
      path_symex(state, tmp_queue);

      // put at head of main queue
      queue.splice(queue.begin(), tmp_queue);
    }
    catch(const std::string &e)
    {
      error() << e << eom;
      number_of_dropped_states++;
    }
    catch(const char *e)
    {
      error() << e << eom;
      number_of_dropped_states++;
    }
    catch(int)
    {
      number_of_dropped_states++;
    }
  }

  report_statistics();

  return number_of_failed_properties==0?resultt::SAFE:resultt::UNSAFE;
}

void path_searcht::report_statistics()
{
  std::size_t number_of_visited_locations=0;
  for(const auto &l : loc_data)
    if(l.visited)
      number_of_visited_locations++;

  #if 0
  for(unsigned l=0; l<loc_data.size(); l++)
    if(!loc_data[l].visited)
      status() << "NV: " << l << eom;
  #endif

  // report a bit
  status() << "Number of visited locations: "
           << number_of_visited_locations << " (out of "
           << number_of_locs << ')' << messaget::eom;

  status() << "Number of dropped states: "
           << number_of_dropped_states << messaget::eom;

  status() << "Number of paths: "
           << number_of_paths << messaget::eom;

  status() << "Number of infeasible paths: "
           << number_of_infeasible_paths << messaget::eom;

  status() << "Generated " << number_of_VCCs << " VCC(s), "
           << number_of_VCCs_after_simplification
           << " remaining after simplification"
           << messaget::eom;

  time_periodt total_time=current_time()-start_time;
  status() << "Runtime: " << total_time << "s total, "
           << sat_time << "s SAT" << messaget::eom;
}

void path_searcht::pick_state()
{
  switch(search_heuristic)
  {
  case search_heuristict::DFS:
    // Picking the first one (most recently added) is a DFS.
    return;

  case search_heuristict::BFS:
    // Picking the last one is a BFS.
    if(queue.size()>=2)
      // move last to first position
      queue.splice(queue.begin(), queue, --queue.end(), queue.end());
    return;

  case search_heuristict::LOCS:
    return;
  }
}

void path_searcht::do_show_vcc(statet &state)
{
  // keep statistics
  number_of_VCCs++;

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  mstreamt &out=result();

  if(instruction.source_location.is_not_nil())
    out << instruction.source_location << '\n';

  if(instruction.source_location.get_comment()!="")
    out << instruction.source_location.get_comment() << '\n';

  unsigned count=1;

  std::vector<path_symex_step_reft> steps;
  state.history.build_history(steps);

  for(const auto &step_ref : steps)
  {
    if(step_ref->guard.is_not_nil())
    {
      std::string string_value=from_expr(ns, "", step_ref->guard);
      out << "{-" << count << "} " << string_value << '\n';
      count++;
    }

    if(step_ref->ssa_rhs.is_not_nil())
    {
      equal_exprt equality(step_ref->ssa_lhs, step_ref->ssa_rhs);
      std::string string_value=from_expr(ns, "", equality);
      out << "{-" << count << "} " << string_value << '\n';
      count++;
    }
  }

  out << "|--------------------------" << '\n';

  exprt assertion=state.read(instruction.guard);

  out << "{" << 1 << "} "
      << from_expr(ns, "", assertion) << '\n';

  if(!assertion.is_true())
    number_of_VCCs_after_simplification++;

  out << eom;
}

/// decide whether to drop a state
bool path_searcht::drop_state(const statet &state)
{
  goto_programt::const_targett pc=state.get_instruction();

  const source_locationt &source_location=pc->source_location;

  if(!source_location.is_nil() &&
     last_source_location!=source_location)
  {
    debug() << "SYMEX at file " << source_location.get_file()
            << " line " << source_location.get_line()
            << " function " << source_location.get_function()
            << eom;

    last_source_location=source_location;
  }

  // depth limit
  if(state.get_depth()>=depth_limit)
    return true;

  // context bound
  if(state.get_no_thread_interleavings()>=context_bound)
    return true;

  // branch bound
  if(state.get_no_branches()>=branch_bound)
    return true;

  // unwinding limit -- loops
  if(unwind_limit!=std::numeric_limits<unsigned>::max() && 
     pc->is_backwards_goto())
  {
    bool stop=false;

    for(const auto &loop_info : state.unwinding_map)
      if(loop_info.second>=unwind_limit)
      {
        stop=true;
        break;
      }

    const irep_idt id=goto_programt::loop_id(pc);
    path_symex_statet::unwinding_mapt::const_iterator entry=
      state.unwinding_map.find(state.pc());
    debug() << (stop?"Not unwinding":"Unwinding")
      << " loop " << id << " iteration "
      << (entry==state.unwinding_map.end()?-1:entry->second)
      << " (" << unwind_limit << " max)"
      << " " << source_location
      << " thread " << state.get_current_thread() << eom;

    if(stop)
      return true;
  }

  // unwinding limit -- recursion
  if(unwind_limit!=std::numeric_limits<unsigned>::max() &&
     pc->is_function_call())
  {
    bool stop=false;

    for(const auto &rec_info : state.recursion_map)
      if(rec_info.second>=unwind_limit)
      {
        stop=true;
        break;
      }

    exprt function=to_code_function_call(pc->code).function();
    const irep_idt id=function.get(ID_identifier); // could be nil
    path_symex_statet::recursion_mapt::const_iterator entry=
      state.recursion_map.find(id);
    if(entry!=state.recursion_map.end())
      debug() << (stop?"Not unwinding":"Unwinding")
        << " recursion " << id << " iteration "
        << entry->second
        << " (" << unwind_limit << " max)"
        << " " << source_location
        << " thread " << state.get_current_thread() << eom;

    if(stop)
      return true;
  }

  // search time limit (--max-search-time)
  if(time_limit!=std::numeric_limits<unsigned>::max() &&
     current_time().get_t()>start_time.get_t()+time_limit*1000)
    return true;

  if(pc->is_assume() &&
     simplify_expr(pc->guard, ns).is_false())
  {
    debug() << "aborting path on assume(false) at "
            << pc->source_location
            << " thread " << state.get_current_thread();

    const irep_idt &c=pc->source_location.get_comment();
    if(!c.empty())
      debug() << ": " << c;

    debug() << eom;

    return true;
  }

  return false;
}

void path_searcht::check_assertion(statet &state)
{
  // keep statistics
  number_of_VCCs++;

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  irep_idt property_name=instruction.source_location.get_property_id();
  property_entryt &property_entry=property_map[property_name];

  if(property_entry.status==FAILURE)
    return; // already failed
  else if(property_entry.status==NOT_REACHED)
    property_entry.status=SUCCESS; // well, for now!

  // the assertion in SSA
  exprt assertion=
    state.read(instruction.guard);

  if(assertion.is_true())
    return; // no error, trivially

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
    property_entry.status=FAILURE;
    number_of_failed_properties++;
  }

  sat_time+=current_time()-sat_start_time;
}

bool path_searcht::is_feasible(statet &state)
{
  status() << "Feasibility check" << eom;

  // take the time
  absolute_timet sat_start_time=current_time();

  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);

  satcheck.set_message_handler(get_message_handler());
  bv_pointers.set_message_handler(get_message_handler());

  bool result=state.is_feasible(bv_pointers);

  sat_time+=current_time()-sat_start_time;

  return result;
}

void path_searcht::initialize_property_map(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(!it->second.is_inlined())
    {
      const goto_programt &goto_program=it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location=i_it->source_location;

        irep_idt property_name=source_location.get_property_id();

        property_entryt &property_entry=property_map[property_name];
        property_entry.status=NOT_REACHED;
        property_entry.description=source_location.get_comment();
        property_entry.source_location=source_location;
      }
    }
}
