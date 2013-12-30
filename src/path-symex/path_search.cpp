/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "path_symex.h"
#include "build_goto_trace.h"
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
  
  queue.push_back(initial_state(var_map, locs));
  
  while(!queue.empty())
  {
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();
    
    if(!state->is_executable())
    {
      queue.erase(state);
      continue;
    }
    
    status() << "Queue " << queue.size()
             << " thread " << state->get_current_thread()
             << "/" << state->threads.size()
             << " PC " << state->pc() << messaget::eom;

    // an error, possibly?
    if(state->get_instruction()->is_assert())
      if(check_assertion(*state, ns))
        return UNSAFE; // property fails
    
    // execute
    path_symex(*state, queue, ns);
  }

  return SAFE; // property holds
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
  const goto_programt::instructiont &instruction=
    *state.get_instruction();
    
  mstreamt &out=result();

  if(instruction.location.is_not_nil())
    out << instruction.location << "\n";
  
  if(instruction.location.get_comment()!="")
    out << instruction.location.get_comment() << "\n";
    
  unsigned count=1;

  for(path_symex_historyt::stepst::const_iterator
      s_it=state.history.steps.begin();
      s_it!=state.history.steps.end();
      s_it++)
  {      
    if(s_it->guard.is_not_nil())
    {
      std::string string_value=from_expr(ns, "", s_it->guard);
      out << "{-" << count << "} " << string_value << "\n";
      count++;
    }

    if(s_it->ssa_rhs.is_not_nil())
    {
      equal_exprt equality(s_it->ssa_lhs, s_it->ssa_rhs);
      std::string string_value=from_expr(ns, "", equality);
      out << "{-" << count << "} " << string_value << "\n";
      count++;
    }
  }

  out << "|--------------------------" << "\n";

  out << "{" << 1 << "} "
      << from_expr(ns, "", state.read(instruction.guard)) << "\n";
  
  out << eom;
}

/*******************************************************************\

Function: path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_searcht::check_assertion(
  statet &state,
  const namespacet &ns)
{
  if(show_vcc)
  {
    do_show_vcc(state, ns);
    return false; // no error
  }

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);

  // the path constraint
  bv_pointers << state.history;

  // the assertion in SSA
  exprt assertion=
    state.read(instruction.guard);

  // negate  
  bv_pointers.set_to(assertion, false);
  
  switch(bv_pointers.dec_solve())
  {
  case decision_proceduret::D_SATISFIABLE:
    build_goto_trace(state, bv_pointers, error_trace);
    return true; // error
  
  case decision_proceduret::D_UNSATISFIABLE:
    return false; // no error
  
  default:
    throw "error from solver";
  }
}
