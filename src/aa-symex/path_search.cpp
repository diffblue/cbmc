/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

\*******************************************************************/

#include <cerrno>
#include <util/time_stopping.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <aa-path-symex/path_symex.h>
#include <aa-path-symex/build_goto_trace.h>

#include "path_search.h"

#ifdef PATH_SYMEX_FORK
// we've already check that the platform is (mostly) POSIX-compliant
#include <sys/wait.h>
#endif

/*******************************************************************\

Function: path_searcht::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_searcht::resultt path_searcht::operator()(
  const goto_functionst &goto_functions)
{
#ifdef PATH_SYMEX_FORK
  // Disable output because there is no meaningful way
  // to write text when multiple path_search processes
  // run concurrently. This could be remedied by piping
  // to individual files or inter-process communication,
  // a performance bottleneck, however.
  null_message_handlert null_message;
  set_message_handler(null_message);
#endif

  locst locs(ns);
  var_mapt var_map(ns);

  locs.build(goto_functions);

  // this is the container for the history-forest
  path_symex_historyt history;

  queue.push_back(initial_state(var_map, locs, history));

  // set up the statistics
  number_of_instructions=0;
  number_of_dropped_states=0;
  number_of_paths=0;
  number_of_VCCs=0;
  number_of_VCCs_after_simplification=0;
  number_of_failed_properties=0;
  number_of_fast_forward_steps=0;

  // stop the time
  start_time=current_time();

  initialize_property_map(goto_functions);

  while(!queue.empty())
  {
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();

    // fast forwarding required?
    if(state->is_lazy())
    {
      assert(state->is_executable());
      assert(state->history.is_nil());

      // keep allocated memory, this is faster than
      // instantiating a new empty vector and map
      history.clear();
      var_map.clear();
      state->history=path_symex_step_reft(history);

      // restore all fields of a lazy state by symbolic
      // execution along previously recorded branches
      const queuet::size_type queue_size=queue.size();
      do
      {
        number_of_fast_forward_steps++;

        path_symex(*state, queue);
#ifdef PATH_SYMEX_OUTPUT
        status() << "Fast forward thread " << state->get_current_thread()
                 << "/" << state->threads.size()
                 << " PC " << state->pc() << messaget::eom;
#endif
      }
      while(state->is_lazy() && state->is_executable());
      assert(queue.size() == queue_size);
    }

    // TODO: check lazy states before fast forwarding, or perhaps it
    // is better to even check before inserting into queue
    if(drop_state(*state))
    {
      number_of_dropped_states++;
      queue.erase(state);
      continue;
    }

    if(!state->is_executable())
    {
      queue.erase(state);
      continue;
    }

    // count only executable instructions
    number_of_instructions++;

#ifdef PATH_SYMEX_OUTPUT
    status() << "Queue " << queue.size()
             << " thread " << state->get_current_thread()
             << "/" << state->threads.size()
             << " PC " << state->pc() << messaget::eom;
#endif

    // an error, possibly?
    if(state->get_instruction()->is_assert())
    {
      if(show_vcc)
        do_show_vcc(*state);
      else
      {
        check_assertion(*state);

        // all assertions failed?
        if(number_of_failed_properties==property_map.size())
          break;
      }
    }

#ifdef PATH_SYMEX_FORK
    if(try_await())
    {
      debug() << "Child process has terminated "
                 "so exit parent" << messaget::eom;
      break;
    }
#endif

    // execute and record whether a "branch" occurred
    const queuet::size_type queue_size = queue.size();
    path_symex(*state, queue);

    assert(queue_size <= queue.size());
    number_of_paths += (queue.size() - queue_size);
  }

#ifdef PATH_SYMEX_FORK
  int exit_status=await();
  if(exit_status==0 && number_of_failed_properties!=0)
  {
    // the eldest child process (if any) reports found bugs
    report_statistics();
    return UNSAFE;
  }
  else
  {
    // either a child found and reported a bug or
    // the parent's search partition is safe
    switch(exit_status)
    {
    case 0: return SAFE;
    case 10: return UNSAFE;
    default: return ERROR;
    }
  }
#else
  report_statistics();

  return number_of_failed_properties==0?SAFE:UNSAFE;
#endif
}

#ifdef PATH_SYMEX_FORK
/*******************************************************************\

Function: path_searcht::await()

  Inputs:

 Outputs: returns zero if and only if every child process succeeds;
          otherwise, the error of exactly one child is returned

 Purpose: POSIX-compliant (possibly blocking) wait on child
          processes, writes to error() if anything goes wrong;
          any earlier calls to try_await() do not affect await()

\*******************************************************************/

int path_searcht::await()
{
  int status;
  for(;;)
  {
    // a process' entries for its child processes are deleted after
    // the first call to waitpid(). When waitpid() is called again
    // it returns -1 and errno is set to ECHILD.
    pid_t pid=wait(&status);
    if(pid==-1)
    {
      if(errno==ECHILD)
        break; // no more child processes
    }
    else
    {
      if(!WIFEXITED(status) || WEXITSTATUS(status)!=0)
      {
        debug() << "PID " << pid << " failed, return code "
                << WEXITSTATUS(status) << messaget::eom;

        return WEXITSTATUS(status);
      }
    }
  }

  return 0;
}

/*******************************************************************\

Function: path_searcht::try_await()

  Inputs:

 Outputs: returns true if and only if at least one child process
          has terminated

 Purpose: POSIX-compliant nonblocking wait on child processes,
          child's status is preserved for await() function

\*******************************************************************/

bool path_searcht::try_await()
{
  int status;
  pid_t pid=waitpid(-1, &status, WNOHANG | WNOWAIT);
  return pid!=-1;
}
#endif

/*******************************************************************\

Function: path_searcht::report_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::report_statistics()
{
  // report a bit

  status() << "Number of instructions: "
           << number_of_instructions << messaget::eom;

  status() << "Number of dropped states: "
           << number_of_dropped_states << messaget::eom;

  status() << "Number of paths: "
           << number_of_paths << messaget::eom;

  status() << "Number of fast forward steps: "
           << number_of_fast_forward_steps << messaget::eom;

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

/*******************************************************************\

Function: path_searcht::drop_state

  Inputs:

 Outputs:

 Purpose: decide whether to drop a state

\*******************************************************************/

bool path_searcht::drop_state(const statet &state) const
{
  // depth limit
  if(depth_limit_set && state.get_depth()>depth_limit)
    return true;

  // context bound
  if(context_bound_set && state.get_no_thread_interleavings()>context_bound)
    return true;


  // unwinding limit -- loops
  if(unwind_limit_set && state.get_instruction()->is_backwards_goto())
  {
    for(const auto &loop_info : state.unwinding_map)
      if(loop_info.second>unwind_limit)
        return true;
  }

  // unwinding limit -- recursion
  if(unwind_limit_set && state.get_instruction()->is_function_call())
  {
    for(const auto &rec_info : state.recursion_map)
      if(rec_info.second>unwind_limit)
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

/*******************************************************************\

Function: path_searcht::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
