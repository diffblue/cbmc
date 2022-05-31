/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#include "ai.h"

#include <memory>
#include <sstream>
#include <type_traits>

#include <util/invariant.h>
#include <util/std_code.h>

void ai_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  for(const auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << gf_entry.first << "\n";
      out << "////\n";
      out << "\n";

      output(ns, gf_entry.first, gf_entry.second.body, out);
    }
  }
}

void ai_baset::output(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_programt &goto_program,
  std::ostream &out) const
{
  (void)function_id; // unused parameter

  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " " << i_it->source_location()
        << "\n";

    abstract_state_before(i_it)->output(out, *this, ns);
    out << "\n";
    #if 1
    i_it->output(out);
    out << "\n";
    #endif
  }
}

jsont ai_baset::output_json(
  const namespacet &ns,
  const goto_functionst &goto_functions) const
{
  json_objectt result;

  for(const auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
    {
      result[id2string(gf_entry.first)] =
        output_json(ns, gf_entry.first, gf_entry.second.body);
    }
    else
    {
      result[id2string(gf_entry.first)] = json_arrayt();
    }
  }

  return std::move(result);
}

jsont ai_baset::output_json(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_programt &goto_program) const
{
  (void)function_id; // unused parameter

  json_arrayt contents;

  forall_goto_program_instructions(i_it, goto_program)
  {
    // Ideally we need output_instruction_json
    std::ostringstream out;
    i_it->output(out);

    json_objectt location{
      {"locationNumber", json_numbert(std::to_string(i_it->location_number))},
      {"sourceLocation", json_stringt(i_it->source_location().as_string())},
      {"abstractState", abstract_state_before(i_it)->output_json(*this, ns)},
      {"instruction", json_stringt(out.str())}};

    contents.push_back(std::move(location));
  }

  return std::move(contents);
}

xmlt ai_baset::output_xml(
  const namespacet &ns,
  const goto_functionst &goto_functions) const
{
  xmlt program("program");

  for(const auto &gf_entry : goto_functions.function_map)
  {
    xmlt function(
      "function",
      {{"name", id2string(gf_entry.first)},
       {"body_available", gf_entry.second.body_available() ? "true" : "false"}},
      {});

    if(gf_entry.second.body_available())
    {
      function.new_element(
        output_xml(ns, gf_entry.first, gf_entry.second.body));
    }

    program.new_element(function);
  }

  return program;
}

xmlt ai_baset::output_xml(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_programt &goto_program) const
{
  (void)function_id; // unused parameter

  xmlt function_body;

  forall_goto_program_instructions(i_it, goto_program)
  {
    xmlt location(
      "",
      {{"location_number", std::to_string(i_it->location_number)},
       {"source_location", i_it->source_location().as_string()}},
      {abstract_state_before(i_it)->output_xml(*this, ns)});

    // Ideally we need output_instruction_xml
    std::ostringstream out;
    i_it->output(out);
    location.set_attribute("instruction", out.str());

    function_body.new_element(location);
  }

  return function_body;
}

ai_baset::trace_ptrt
ai_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'

  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    return entry_state(f_it->second.body);

  // It is not clear if this is even a well-structured goto_functionst object
  return nullptr;
}

ai_baset::trace_ptrt ai_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point
  trace_ptrt p = history_factory->epoch(goto_program.instructions.begin());
  get_state(p).make_entry();
  return p;
}

void ai_baset::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  initialize(function_id, goto_function.body);
}

void ai_baset::initialize(const irep_idt &, const goto_programt &goto_program)
{
  // Domains are created and set to bottom on access.
  // So we do not need to set them to be bottom before hand.
}

void ai_baset::initialize(const goto_functionst &goto_functions)
{
  for(const auto &gf_entry : goto_functions.function_map)
    initialize(gf_entry.first, gf_entry.second);
}

void ai_baset::finalize()
{
  // Nothing to do per default
}

ai_baset::trace_ptrt ai_baset::get_next(working_sett &working_set)
{
  PRECONDITION(!working_set.empty());

  static_assert(
    std::is_same<
      working_sett,
      std::set<trace_ptrt, ai_history_baset::compare_historyt>>::value,
    "begin must return the minimal entry");
  auto first = working_set.begin();

  trace_ptrt t = *first;

  working_set.erase(first);

  return t;
}

bool ai_baset::fixedpoint(
  trace_ptrt start_trace,
  const irep_idt &function_id,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  PRECONDITION(start_trace != nullptr);

  working_sett working_set;
  put_in_working_set(working_set, start_trace);

  bool new_data=false;

  while(!working_set.empty())
  {
    trace_ptrt p = get_next(working_set);

    // goto_program is really only needed for iterator manipulation
    if(visit(function_id, p, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

void ai_baset::fixedpoint(
  trace_ptrt start_trace,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  goto_functionst::function_mapt::const_iterator f_it =
    goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it != goto_functions.function_map.end())
    fixedpoint(start_trace, f_it->first, f_it->second.body, goto_functions, ns);
}

bool ai_baset::visit(
  const irep_idt &function_id,
  trace_ptrt p,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;
  locationt l = p->current_location();
  messaget log(message_handler);

  log.progress() << "ai_baset::visit " << l->location_number << " in "
                 << function_id << messaget::eom;

  // Function call and end are special cases
  if(l->is_function_call())
  {
    DATA_INVARIANT(
      goto_program.get_successors(l).size() == 1,
      "function calls only have one successor");

    DATA_INVARIANT(
      *(goto_program.get_successors(l).begin()) == std::next(l),
      "function call successor / return location must be the next instruction");

    new_data = visit_function_call(
      function_id, p, working_set, goto_program, goto_functions, ns);
  }
  else if(l->is_end_function())
  {
    DATA_INVARIANT(
      goto_program.get_successors(l).empty(),
      "The end function instruction should have no successors.");

    new_data = visit_end_function(
      function_id, p, working_set, goto_program, goto_functions, ns);
  }
  else
  {
    // Successors can be empty, for example assume(0).
    // Successors can contain duplicates, for example GOTO next;
    for(const auto &to_l : goto_program.get_successors(l))
    {
      if(to_l == goto_program.instructions.end())
        continue;

      new_data |= visit_edge(
        function_id,
        p,
        function_id,
        to_l,
        ai_history_baset::no_caller_history,
        ns,
        working_set); // Local steps so no caller history needed
    }
  }

  return new_data;
}

bool ai_baset::visit_edge(
  const irep_idt &function_id,
  trace_ptrt p,
  const irep_idt &to_function_id,
  locationt to_l,
  trace_ptrt caller_history,
  const namespacet &ns,
  working_sett &working_set)
{
  messaget log(message_handler);
  log.progress() << "ai_baset::visit_edge from "
                 << p->current_location()->location_number << " to "
                 << to_l->location_number << "... ";

  // Has history taught us not to step here...
  auto next =
    p->step(to_l, *(storage->abstract_traces_before(to_l)), caller_history);
  if(next.first == ai_history_baset::step_statust::BLOCKED)
  {
    log.progress() << "blocked by history" << messaget::eom;
    return false;
  }
  else if(next.first == ai_history_baset::step_statust::NEW)
  {
    log.progress() << "gives a new history... ";
  }
  else
  {
    log.progress() << "merges with existing history... ";
  }
  trace_ptrt to_p = next.second;

  // Abstract domains are mutable so we must copy before we transform
  statet &current = get_state(p);

  std::unique_ptr<statet> tmp_state(make_temporary_state(current));
  statet &new_values = *tmp_state;

  // Apply transformer
  log.progress() << "applying transformer... ";
  new_values.transform(function_id, p, to_function_id, to_p, *this, ns);

  // Expanding a domain means that it has to be analysed again
  // Likewise if the history insists that it is a new trace
  // (assuming it is actually reachable).
  log.progress() << "merging... ";
  bool return_value = false;
  if(
    merge(new_values, p, to_p) ||
    (next.first == ai_history_baset::step_statust::NEW &&
     !new_values.is_bottom()))
  {
    put_in_working_set(working_set, to_p);
    log.progress() << "result queued." << messaget::eom;
    return_value = true;
  }
  else
  {
    log.progress() << "domain unchanged." << messaget::eom;
  }

  // Branch because printing some histories and domains can be expensive
  // esp. if the output is then just discarded and this is a critical path.
  if(message_handler.get_verbosity() >= messaget::message_levelt::M_DEBUG)
  {
    log.debug() << "p = ";
    p->output(log.debug());
    log.debug() << messaget::eom;

    log.debug() << "current = ";
    current.output(log.debug(), *this, ns);
    log.debug() << messaget::eom;

    log.debug() << "to_p = ";
    to_p->output(log.debug());
    log.debug() << messaget::eom;

    log.debug() << "new_values = ";
    new_values.output(log.debug(), *this, ns);
    log.debug() << messaget::eom;
  }

  return return_value;
}

bool ai_baset::visit_edge_function_call(
  const irep_idt &calling_function_id,
  trace_ptrt p_call,
  locationt l_return,
  const irep_idt &,
  working_sett &working_set,
  const goto_programt &,
  const goto_functionst &,
  const namespacet &ns)
{
  messaget log(message_handler);
  log.progress() << "ai_baset::visit_edge_function_call from "
                 << p_call->current_location()->location_number << " to "
                 << l_return->location_number << messaget::eom;

  // The default implementation is not interprocedural
  // so the effects of the call are approximated but nothing else
  return visit_edge(
    calling_function_id,
    p_call,
    calling_function_id,
    l_return,
    ai_history_baset::
      no_caller_history, // Not needed as we are skipping the function call
    ns,
    working_set);
}

bool ai_baset::visit_function_call(
  const irep_idt &calling_function_id,
  trace_ptrt p_call,
  working_sett &working_set,
  const goto_programt &caller,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  locationt l_call = p_call->current_location();

  PRECONDITION(l_call->is_function_call());

  messaget log(message_handler);
  log.progress() << "ai_baset::visit_function_call at "
                 << l_call->location_number << messaget::eom;

  locationt l_return = std::next(l_call);

  // operator() allows analysis of a single goto_program independently
  // it generates a synthetic goto_functions object for this
  if(!goto_functions.function_map.empty())
  {
    const exprt &callee_expression = l_call->call_function();

    if(callee_expression.id() == ID_symbol)
    {
      const irep_idt &callee_function_id =
        to_symbol_expr(callee_expression).get_identifier();

      log.progress() << "Calling " << callee_function_id << messaget::eom;

      goto_functionst::function_mapt::const_iterator it =
        goto_functions.function_map.find(callee_function_id);

      DATA_INVARIANT(
        it != goto_functions.function_map.end(),
        "Function " + id2string(callee_function_id) + "not in function map");

      const goto_functionst::goto_functiont &callee_fun = it->second;

      if(callee_fun.body_available())
      {
        return visit_edge_function_call(
          calling_function_id,
          p_call,
          l_return,
          callee_function_id,
          working_set,
          callee_fun.body,
          goto_functions,
          ns);
      }
      else
      {
        // Fall through to the default, body not available, case
      }
    }
    else
    {
      // Function pointers are not currently supported and must be removed
      DATA_INVARIANT(
        callee_expression.id() == ID_symbol,
        "Function pointers and indirect calls must be removed before "
        "analysis.");
    }
  }

  // If the body is not available then we just do the edge from call to return
  // in the caller.  Domains should over-approximate what the function might do.
  return visit_edge(
    calling_function_id,
    p_call,
    calling_function_id,
    l_return,
    ai_history_baset::no_caller_history, // Would be the same as p_call...
    ns,
    working_set);
}

bool ai_baset::visit_end_function(
  const irep_idt &function_id,
  trace_ptrt p,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  locationt l = p->current_location();
  PRECONDITION(l->is_end_function());

  messaget log(message_handler);
  log.progress() << "ai_baset::visit_end_function " << function_id
                 << messaget::eom;

  // Do nothing
  return false;
}

bool ai_recursive_interproceduralt::visit_edge_function_call(
  const irep_idt &calling_function_id,
  trace_ptrt p_call,
  locationt l_return,
  const irep_idt &callee_function_id,
  working_sett &working_set,
  const goto_programt &callee,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  messaget log(message_handler);
  log.progress() << "ai_recursive_interproceduralt::visit_edge_function_call"
                 << " from " << p_call->current_location()->location_number
                 << " to " << l_return->location_number << messaget::eom;

  // This is the edge from call site to function head.
  {
    locationt l_begin = callee.instructions.begin();

    working_sett catch_working_set; // The trace from the next fixpoint

    // Do the edge from the call site to the beginning of the function
    bool new_data = visit_edge(
      calling_function_id,
      p_call,
      callee_function_id,
      l_begin,
      ai_history_baset::
        no_caller_history, // Not needed as p_call already has the info
      ns,
      catch_working_set);

    log.progress() << "Handle " << callee_function_id << " recursively"
                   << messaget::eom;

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(
        get_next(catch_working_set),
        callee_function_id,
        callee,
        goto_functions,
        ns);
  }

  // This is the edge from function end to return site.
  {
    log.progress() << "Handle return edges" << messaget::eom;

    // get location at end of the procedure we have called
    locationt l_end = --callee.instructions.end();
    DATA_INVARIANT(
      l_end->is_end_function(),
      "The last instruction of a goto_program must be END_FUNCTION");

    // Find the histories for a location
    auto traces = storage->abstract_traces_before(l_end);

    bool new_data = false;

    // The history used may mean there are multiple histories at the end of the
    // function.  Some of these can be progressed (for example, if the history
    // tracks paths within functions), some can't be (for example, not all
    // calling contexts will be appropriate).  We rely on the history's step,
    // called from visit_edge to prune as applicable.
    for(auto p_end : *traces)
    {
      // do edge from end of function to instruction after call
      const statet &end_state = get_state(p_end);

      if(!end_state.is_bottom())
      {
        // function exit point reachable in that history

        new_data |= visit_edge(
          callee_function_id,
          p_end,
          calling_function_id,
          l_return,
          p_call, // To allow function-local history
          ns,
          working_set);
      }
    }

    return new_data;
  }
}
