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

  // Find the histories at the end of the function
  auto traces = storage->abstract_traces_before(l_callee_end);

  bool new_data = false; // Whether we have changed a domain in the caller

  // As with recursive-interprocedural, there are potentially multiple histories
  // at the end, or maybe none.  Only some of these will be 'descendents' of
  // p_call_site and p_callee_start
  for(auto p_callee_end : *traces)
  {
    // First off, is it even reachable?
    const statet &s_callee_end = get_state(p_callee_end);

    if(s_callee_end.is_bottom())
      continue; // Unreachable in callee -- no need to merge

    // Can it return to p_call_site?
    auto return_step = p_callee_end->step(
      l_return_site,
      *(storage->abstract_traces_before(l_return_site)),
      p_call_site); // Because it is a return edge!
    if(return_step.first == ai_history_baset::step_statust::BLOCKED)
      continue; // Can't return -- no need to merge

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
    s_working.transform(
      callee_function_id,
      l_callee_end,
      calling_function_id,
      l_return_site,
      *this,
      ns);

    // TODO : this is probably needed to avoid three_way_merge modifying one of
    // it's arguments as it goes.  A better solution would be to refactor
    // merge_three_way_function_return.
    const std::unique_ptr<statet> ptr_s_working_copy(
      make_temporary_state(s_working));

    s_working.merge_three_way_function_return(
      get_state(p_call_site),
      get_state(p_callee_start),
      *ptr_s_working_copy,
      ns);

    if(
      merge(s_working, p_callee_end, p_return_site) ||
      (return_step.first == ai_history_baset::step_statust::NEW &&
       !s_working.is_bottom()))
    {
      put_in_working_set(working_set, p_return_site);
      new_data = true;
    }
  }

  return new_data;
}

#if 0
   // This is the edge from function end to return site.
 
   {
     if(end_state.is_bottom())
       return false; // function exit point not reachable
 
     working_sett working_set; // Redundant; visit will add l_return
 
-    return visit_edge(
-      f_it->first, l_end, calling_function_id, l_return, ns, working_set);
+    const std::unique_ptr<statet> tmp_state(make_temporary_state(end_state));
+    tmp_state->transform(f_it->first, l_end, f_it->first, l_return, *this, ns);
+
+    const std::unique_ptr<statet> pre_merge_state{
+      make_temporary_state(*tmp_state)};
+
+    const locationt l_begin = goto_function.body.instructions.begin();
+    tmp_state->merge_three_way_function_return(
+      get_state(l_call), get_state(l_begin), *pre_merge_state, ns);
+
+    return merge(*tmp_state, l_end, l_return);
   }

#endif

#if 0
bool ai_baset::visit_edge(
  const irep_idt &function_id,
  trace_ptrt p,
  const irep_idt &to_function_id,
  locationt to_l,
  trace_ptrt caller_history,
  const namespacet &ns,
  working_sett &working_set)
{
  // We only care about the return cases
  if (caller_history == ai_history_baset::no_caller_history) {
    return ai_recursive_interproceduralt::visit_edge(function_id, p, to_function_id, to_l, caller_history, ns, working_set);
  }

  // There are four histories / locations / domains we care about
  // In chronological order...

  trace_ptr call_site_history = caller_history;
  statet &call_site_state = get_state(call_site_history);
  locationt call_site_location = call_site_history.current_location();
  INVARIANT(call_site_location->is_function_call(), "caller_history implies that is is a function call");

  trace_ptr callee_start_history = TBD;
  statet &callee_start_state = get_state(callee_start_history);
  locationt callee_start_location = callee_start_history.current_location();

  trace_ptr callee_end_history = p;
  statet &callee_end_state = get_state(callee_end_history);
  locationt callee_end_location = callee_end_history.current_location();
  INVARIANT(callee_end_location->is_end_function(), "TBD");

  trace_ptr return_site_history = STEP;
  statet &return_site_state = get_state(return_site_history);
  locationt return_site_location = to_l;
  INVARIANT(std::next(call_site_location) == to_l, "TBD");


  
  // Has history taught us not to step here...
  auto next =
    p->step(to_l, *(storage->abstract_traces_before(to_l)), caller_history);
  if(next.first == ai_history_baset::step_statust::BLOCKED)
    return false;
  trace_ptrt to_p = next.second;

  // Abstract domains are mutable so we must copy before we transform
  statet &current = get_state(p);

  std::unique_ptr<statet> tmp_state(make_temporary_state(current));
  statet &new_values = *tmp_state;

  // Apply transformer
  new_values.transform(function_id, p, to_function_id, to_p, *this, ns);

  // Expanding a domain means that it has to be analysed again
  // Likewise if the history insists that it is a new trace
  // (assuming it is actually reachable).
  if(
    merge(new_values, p, to_p) ||
    (next.first == ai_history_baset::step_statust::NEW &&
     !new_values.is_bottom()))
  {
    put_in_working_set(working_set, to_p);
    return true;
  }

  return false;
}

#endif
