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

#include <util/invariant.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include "is_threaded.h"

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

      output(ns, f_it->second.body, f_it->first, out);
    }
  }
}

void ai_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    abstract_state_before(i_it)->output(out, *this, ns);
    out << "\n";
    #if 1
    goto_program.output_instruction(ns, identifier, out, *i_it);
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
      result[id2string(f_it->first)]=
        output_json(ns, f_it->second.body, f_it->first);
    }
    else
    {
      result[id2string(f_it->first)]=json_arrayt();
    }
  }

  return std::move(result);
}

/// Output the domains for a single function as JSON
/// \param ns: The namespace
/// \param goto_program: The goto program
/// \param identifier: The identifier used to find a symbol to identify the
///   source language
/// \return The JSON object
jsont ai_baset::output_json(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier) const
{
  json_arrayt contents;

  forall_goto_program_instructions(i_it, goto_program)
  {
    json_objectt location;
    location["locationNumber"]=
      json_numbert(std::to_string(i_it->location_number));
    location["sourceLocation"]=
      json_stringt(i_it->source_location.as_string());
    location["abstractState"] =
      abstract_state_before(i_it)->output_json(*this, ns);

    // Ideally we need output_instruction_json
    std::ostringstream out;
    goto_program.output_instruction(ns, identifier, out, *i_it);
    location["instruction"]=json_stringt(out.str());

    contents.push_back(location);
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
    xmlt function("function");
    function.set_attribute("name", id2string(f_it->first));
    function.set_attribute(
      "body_available",
      f_it->second.body_available() ? "true" : "false");

    if(f_it->second.body_available())
    {
      function.new_element(output_xml(ns, f_it->second.body, f_it->first));
    }

    program.new_element(function);
  }

  return program;
}

/// Output the domains for a single function as XML
/// \param ns: The namespace
/// \param goto_program: The goto program
/// \param identifier: The identifier used to find a symbol to identify the
///   source language
/// \return The XML object
xmlt ai_baset::output_xml(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier) const
{
  xmlt function_body;

  forall_goto_program_instructions(i_it, goto_program)
  {
    xmlt location;
    location.set_attribute(
      "location_number",
      std::to_string(i_it->location_number));
    location.set_attribute(
      "source_location",
      i_it->source_location.as_string());

    location.new_element(abstract_state_before(i_it)->output_xml(*this, ns));

    // Ideally we need output_instruction_xml
    std::ostringstream out;
    goto_program.output_instruction(ns, identifier, out, *i_it);
    location.set_attribute("instruction", out.str());

    function_body.new_element(location);
  }

  return function_body;
}

void ai_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'

  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    entry_state(f_it->second.body);
}

void ai_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point
  get_state(goto_program.instructions.begin()).make_entry();
}

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function)
{
  initialize(goto_function.body);
}

void ai_baset::initialize(const goto_programt &goto_program)
{
  // we mark everything as unreachable as starting point

  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it).make_bottom();
}

void ai_baset::initialize(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    initialize(it->second);
}

void ai_baset::finalize()
{
  // Nothing to do per default
}

ai_baset::locationt ai_baset::get_next(
  working_sett &working_set)
{
  PRECONDITION(!working_set.empty());

  working_sett::iterator i=working_set.begin();
  locationt l=i->second;
  working_set.erase(i);

  return l;
}

bool ai_baset::fixedpoint(
  const irep_idt &function_identifier,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  working_sett working_set;

  // Put the first location in the working set
  if(!goto_program.empty())
    put_in_working_set(
      working_set,
      goto_program.instructions.begin());

  bool new_data=false;

  while(!working_set.empty())
  {
    locationt l=get_next(working_set);

    // goto_program is really only needed for iterator manipulation
    if(visit(
         function_identifier, l, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

bool ai_baset::visit(
  const irep_idt &function_identifier,
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;

  statet &current=get_state(l);

  for(const auto &to_l : goto_program.get_successors(l))
  {
    if(to_l==goto_program.instructions.end())
      continue;

    std::unique_ptr<statet> tmp_state(
      make_temporary_state(current));

    statet &new_values=*tmp_state;

    bool have_new_values=false;

    if(l->is_function_call() &&
       !goto_functions.function_map.empty())
    {
      // this is a big special case
      const code_function_callt &code=
        to_code_function_call(l->code);

      if(do_function_call_rec(
           function_identifier,
           l,
           to_l,
           code.function(),
           code.arguments(),
           goto_functions,
           ns))
        have_new_values=true;
    }
    else
    {
      // initialize state, if necessary
      get_state(to_l);

      new_values.transform(
        function_identifier, l, function_identifier, to_l, *this, ns);

      if(merge(new_values, l, to_l))
        have_new_values=true;
    }

    if(have_new_values)
    {
      new_data=true;
      put_in_working_set(working_set, to_l);
    }
  }

  return new_data;
}

bool ai_baset::do_function_call(
  const irep_idt &calling_function_identifier,
  locationt l_call,
  locationt l_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &,
  const namespacet &ns)
{
  // initialize state, if necessary
  get_state(l_return);

  PRECONDITION(l_call->is_function_call());

  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  if(!goto_function.body_available())
  {
    // If we don't have a body, we just do an edge call -> return
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(
      calling_function_identifier,
      l_call,
      calling_function_identifier,
      l_return,
      *this,
      ns);

    return merge(*tmp_state, l_call, l_return);
  }

  assert(!goto_function.body.instructions.empty());

  // This is the edge from call site to function head.

  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    // initialize state, if necessary
    get_state(l_begin);

    // do the edge from the call site to the beginning of the function
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(
      calling_function_identifier, l_call, f_it->first, l_begin, *this, ns);

    bool new_data=false;

    // merge the new stuff
    if(merge(*tmp_state, l_call, l_begin))
      new_data=true;

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(f_it->first, goto_function.body, goto_functions, ns);
  }

  // This is the edge from function end to return site.

  {
    // get location at end of the procedure we have called
    locationt l_end=--goto_function.body.instructions.end();
    assert(l_end->is_end_function());

    // do edge from end of function to instruction after call
    const statet &end_state=get_state(l_end);

    if(end_state.is_bottom())
      return false; // function exit point not reachable

    std::unique_ptr<statet> tmp_state(make_temporary_state(end_state));
    tmp_state->transform(
      f_it->first, l_end, calling_function_identifier, l_return, *this, ns);

    // Propagate those
    return merge(*tmp_state, l_end, l_return);
  }
}

bool ai_baset::do_function_call_rec(
  const irep_idt &calling_function_identifier,
  locationt l_call,
  locationt l_return,
  const exprt &function,
  const exprt::operandst &arguments,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  PRECONDITION(!goto_functions.function_map.empty());

  // This is quite a strong assumption on the well-formedness of the program.
  // It means function pointers must be removed before use.
  DATA_INVARIANT(
    function.id() == ID_symbol,
    "Function pointers and indirect calls must be removed before analysis.");

  bool new_data=false;

  const irep_idt &identifier = to_symbol_expr(function).get_identifier();

  goto_functionst::function_mapt::const_iterator it =
    goto_functions.function_map.find(identifier);

  DATA_INVARIANT(
    it != goto_functions.function_map.end(),
    "Function " + id2string(identifier) + "not in function map");

  new_data = do_function_call(
    calling_function_identifier,
    l_call,
    l_return,
    goto_functions,
    it,
    arguments,
    ns);

  return new_data;
}

void ai_baset::sequential_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    fixedpoint(f_it->first, f_it->second.body, goto_functions, ns);
}

void ai_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  sequential_fixedpoint(goto_functions, ns);

  is_threadedt is_threaded(goto_functions);

  // construct an initial shared state collecting the results of all
  // functions
  goto_programt tmp;
  tmp.add_instruction();
  goto_programt::const_targett sh_target=tmp.instructions.begin();
  statet &shared_state=get_state(sh_target);

  struct wl_entryt
  {
    wl_entryt(
      const irep_idt &_function_identifier,
      const goto_programt &_goto_program,
      locationt _location)
      : function_identifier(_function_identifier),
        goto_program(&_goto_program),
        location(_location)
    {
    }

    irep_idt function_identifier;
    const goto_programt *goto_program;
    locationt location;
  };

  typedef std::list<wl_entryt> thread_wlt;
  thread_wlt thread_wl;

  forall_goto_functions(it, goto_functions)
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(is_threaded(t_it))
      {
        thread_wl.push_back(wl_entryt(it->first, it->second.body, t_it));

        goto_programt::const_targett l_end=
          it->second.body.instructions.end();
        --l_end;

        merge_shared(shared_state, l_end, sh_target, ns);
      }
    }

  // now feed in the shared state into all concurrently executing
  // functions, and iterate until the shared state stabilizes
  bool new_shared=true;
  while(new_shared)
  {
    new_shared=false;

    for(const auto &wl_entry : thread_wl)
    {
      working_sett working_set;
      put_in_working_set(working_set, wl_entry.location);

      statet &begin_state = get_state(wl_entry.location);
      merge(begin_state, sh_target, wl_entry.location);

      while(!working_set.empty())
      {
        goto_programt::const_targett l=get_next(working_set);

        visit(
          wl_entry.function_identifier,
          l,
          working_set,
          *(wl_entry.goto_program),
          goto_functions,
          ns);

        // the underlying domain must make sure that the final state
        // carries all possible values; otherwise we would need to
        // merge over each and every state
        if(l->is_end_function())
          new_shared|=merge_shared(shared_state, l, sh_target, ns);
      }
    }
  }
}
