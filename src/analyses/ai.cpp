/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#include "ai.h"

#include <cassert>
#include <memory>
#include <sstream>
#include <type_traits>

#include <util/invariant.h>
#include <util/std_code.h>
#include <util/std_expr.h>

void ai_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << f_it->first << "\n";
      out << "////\n";
      out << "\n";

      output(ns, f_it->first, f_it->second.body, out);
    }
  }
}

void ai_baset::output(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_programt &goto_program,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    abstract_state_before(i_it)->output(out, *this, ns);
    out << "\n";
    #if 1
    goto_program.output_instruction(ns, function_id, out, *i_it);
    out << "\n";
    #endif
  }
}

jsont ai_baset::output_json(
  const namespacet &ns,
  const goto_functionst &goto_functions) const
{
  json_objectt result;

  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available())
    {
      result[id2string(f_it->first)] =
        output_json(ns, f_it->first, f_it->second.body);
    }
    else
    {
      result[id2string(f_it->first)]=json_arrayt();
    }
  }

  return std::move(result);
}

jsont ai_baset::output_json(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_programt &goto_program) const
{
  json_arrayt contents;

  forall_goto_program_instructions(i_it, goto_program)
  {
    // Ideally we need output_instruction_json
    std::ostringstream out;
    goto_program.output_instruction(ns, function_id, out, *i_it);

    json_objectt location{
      {"locationNumber", json_numbert(std::to_string(i_it->location_number))},
      {"sourceLocation", json_stringt(i_it->source_location.as_string())},
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

  forall_goto_functions(f_it, goto_functions)
  {
    xmlt function(
      "function",
      {{"name", id2string(f_it->first)},
       {"body_available", f_it->second.body_available() ? "true" : "false"}},
      {});

    if(f_it->second.body_available())
    {
      function.new_element(output_xml(ns, f_it->first, f_it->second.body));
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
  xmlt function_body;

  forall_goto_program_instructions(i_it, goto_program)
  {
    xmlt location(
      "",
      {{"location_number", std::to_string(i_it->location_number)},
       {"source_location", i_it->source_location.as_string()}},
      {abstract_state_before(i_it)->output_xml(*this, ns)});

    // Ideally we need output_instruction_xml
    std::ostringstream out;
    goto_program.output_instruction(ns, function_id, out, *i_it);
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
  forall_goto_functions(it, goto_functions)
    initialize(it->first, it->second);
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

      new_data |=
        visit_edge(function_id, p, function_id, to_l, ns, working_set);
    }
  }

  return new_data;
}

bool ai_baset::visit_edge(
  const irep_idt &function_id,
  trace_ptrt p,
  const irep_idt &to_function_id,
  locationt to_l,
  const namespacet &ns,
  working_sett &working_set)
{
  // Has history taught us not to step here...
  auto next = p->step(to_l, *(storage->abstract_traces_before(to_l)));
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
  // The default implementation is not interprocedural
  // so the effects of the call are approximated but nothing else
  return visit_edge(
    calling_function_id,
    p_call,
    calling_function_id,
    l_return,
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

  locationt l_return = std::next(l_call);

  // operator() allows analysis of a single goto_program independently
  // it generates a synthetic goto_functions object for this
  if(!goto_functions.function_map.empty())
  {
    const code_function_callt &code = to_code_function_call(l_call->code);
    const exprt &callee_expression = code.function();

    if(callee_expression.id() == ID_symbol)
    {
      const irep_idt &callee_function_id =
        to_symbol_expr(callee_expression).get_identifier();

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
      ns,
      catch_working_set);

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
          ns,
          working_set);
      }
    }

    return new_data;
  }
}
