/*******************************************************************\

Module: Variable sensitivity domain

Author: Martin Brain, martin.brain@cs.ox.ac.uk

Date: August 2020

\*******************************************************************/

/// \file
/// An abstract interpreter, based on the default recursive-interprocedural
/// that uses variable sensitivity domain's three-way-merge operation on
/// returning from a function call.  This gives some of the precision of
/// context-sensitive analysis but at a fraction of the cost.  The really
/// key thing is that it distinguishes between variables that are modified in
/// the function (or things called from it) and those that appear modified
/// because they have different values at different call sites.  This is
/// especially important for preserving the value of (unmodified) global
/// variables.

#include <analyses/variable-sensitivity/three_way_merge_abstract_interpreter.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

bool ai_three_way_merget::visit_edge_function_call(
  const irep_idt &calling_function_id,
  trace_ptrt p_call,
  locationt l_return,
  const irep_idt &callee_function_id,
  working_sett &working_set,
  const goto_programt &callee,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  // There are four locations that matter.
  locationt l_call_site = p_call->current_location();
  locationt l_callee_start = callee.instructions.begin();
  locationt l_callee_end = --callee.instructions.end();
  locationt l_return_site = l_return;

  PRECONDITION(l_call_site->is_function_call());
  DATA_INVARIANT(
    l_callee_end->is_end_function(),
    "The last instruction of a goto_program must be END_FUNCTION");

  messaget log(message_handler);
  log.progress() << "ai_three_way_merget::visit_edge_function_call"
                 << " from " << l_call_site->location_number << " to "
                 << l_callee_start->location_number << messaget::eom;

  // Histories for call_site and callee_start are easy
  trace_ptrt p_call_site = p_call;

  auto next = p_call_site->step(
    l_callee_start,
    *(storage->abstract_traces_before(l_callee_start)),
    ai_history_baset::no_caller_history);
  if(next.first == ai_history_baset::step_statust::BLOCKED)
  {
    // Unexpected...
    // We can't three-way merge without a callee start so
    log.progress() << "Blocked by history step!" << messaget::eom;
    return false;
  }
  trace_ptrt p_callee_start = next.second;

  // Handle the function call recursively
  {
    working_sett catch_working_set; // The starting trace for the next fixpoint

    // Do the edge from the call site to the beginning of the function
    // (This will compute p_callee_start but that is OK)
    bool new_data = visit_edge(
      calling_function_id,
      p_call,
      callee_function_id,
      l_callee_start,
      ai_history_baset::
        no_caller_history, // Not needed as p_call already has the info
      ns,
      catch_working_set);

    log.progress() << "Handle " << callee_function_id << " recursively"
                   << messaget::eom;

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(
        get_next(catch_working_set), // Should be p_callee_start...
        callee_function_id,
        callee,
        goto_functions,
        ns);
  }

  // Now we can give histories for the return part
  log.progress() << "Handle return edges" << messaget::eom;

  // Find the histories at the end of the function
  auto traces = storage->abstract_traces_before(l_callee_end);

  bool new_data = false; // Whether we have changed a domain in the caller

  // As with recursive-interprocedural, there are potentially multiple histories
  // at the end, or maybe none.  Only some of these will be 'descendents' of
  // p_call_site and p_callee_start
  for(auto p_callee_end : *traces)
  {
    log.progress() << "ai_three_way_merget::visit_edge_function_call edge from "
                   << l_callee_end->location_number << " to "
                   << l_return_site->location_number << "... ";

    // First off, is it even reachable?
    const statet &s_callee_end = get_state(p_callee_end);

    if(s_callee_end.is_bottom())
    {
      log.progress() << "unreachable on this trace" << messaget::eom;
      continue; // Unreachable in callee -- no need to merge
    }

    // Can it return to p_call_site?
    auto return_step = p_callee_end->step(
      l_return_site,
      *(storage->abstract_traces_before(l_return_site)),
      p_call_site); // Because it is a return edge!
    if(return_step.first == ai_history_baset::step_statust::BLOCKED)
    {
      log.progress() << "blocked by history" << messaget::eom;
      continue; // Can't return -- no need to merge
    }
    else if(return_step.first == ai_history_baset::step_statust::NEW)
    {
      log.progress() << "gives a new history... ";
    }
    else
    {
      log.progress() << "merges with existing history... ";
    }

    // The fourth history!
    trace_ptrt p_return_site = return_step.second;

    const std::unique_ptr<statet> ptr_s_callee_end_copy(
      make_temporary_state(s_callee_end));
    auto tmp =
      dynamic_cast<variable_sensitivity_domaint *>(&(*ptr_s_callee_end_copy));
    INVARIANT(tmp != nullptr, "Three-way merge requires domain support");
    variable_sensitivity_domaint &s_working = *tmp;

    // Apply transformer
    // This is for an end_function instruction which normally doesn't do much
    // but in VSD it does, so this cannot be omitted.
    log.progress() << "applying transformer... ";
    s_working.transform(
      callee_function_id,
      p_callee_end,
      calling_function_id,
      p_return_site,
      *this,
      ns);

    // TODO : this is probably needed to avoid three_way_merge modifying one of
    // its arguments as it goes.  A better solution would be to refactor
    // merge_three_way_function_return.
    const std::unique_ptr<statet> ptr_s_working_copy(
      make_temporary_state(s_working));

    log.progress() << "three way merge... ";
    s_working.merge_three_way_function_return(
      get_state(p_call_site),
      get_state(p_callee_start),
      *ptr_s_working_copy,
      ns);

    log.progress() << "merging... ";
    if(
      merge(s_working, p_callee_end, p_return_site) ||
      (return_step.first == ai_history_baset::step_statust::NEW &&
       !s_working.is_bottom()))
    {
      put_in_working_set(working_set, p_return_site);
      log.progress() << "result queued." << messaget::eom;
      new_data = true;
    }
    else
    {
      log.progress() << "domain unchanged." << messaget::eom;
    }

    // Branch because printing some histories and domains can be expensive
    // esp. if the output is then just discarded and this is a critical path.
    if(message_handler.get_verbosity() >= messaget::message_levelt::M_DEBUG)
    {
      log.debug() << "p_callee_end = ";
      p_callee_end->output(log.debug());
      log.debug() << messaget::eom;

      log.debug() << "s_callee_end = ";
      s_callee_end.output(log.debug(), *this, ns);
      log.debug() << messaget::eom;

      log.debug() << "p_return_site = ";
      p_return_site->output(log.debug());
      log.debug() << messaget::eom;

      log.debug() << "s_working = ";
      s_working.output(log.debug(), *this, ns);
      log.debug() << messaget::eom;
    }
  }

  return new_data;
}
