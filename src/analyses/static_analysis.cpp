/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <memory>

#include <util/std_expr.h>
#include <util/std_code.h>

#include "is_threaded.h"

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include "static_analysis.h"

/*******************************************************************\

Function: static_analysis_baset::get_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt static_analysis_baset::get_guard(
  locationt from,
  locationt to)
{
  if(!from->is_goto())
    return true_exprt();

  locationt next=from;
  next++;

  if(next==to)
  {
    exprt tmp(from->guard);
    tmp.make_not();
    return tmp;
  }

  return from->guard;
}

/*******************************************************************\

Function: static_analysis_baset::get_return_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt static_analysis_baset::get_return_lhs(locationt to)
{
  // get predecessor of "to"

  to--;

  if(to->is_end_function())
    return static_cast<const exprt &>(get_nil_irep());

  // must be the function call
  assert(to->is_function_call());

  const code_function_callt &code=
    to_code_function_call(to->code);

  return code.lhs();
}

/*******************************************************************\

Function: static_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::operator()(
  const goto_functionst &goto_functions)
{
  initialize(goto_functions);
  fixedpoint(goto_functions);
}

/*******************************************************************\

Function: static_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::operator()(
  const goto_programt &goto_program)
{
  initialize(goto_program);
  goto_functionst goto_functions;
  fixedpoint(goto_program, goto_functions);
}

/*******************************************************************\

Function: static_analysis_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::output(
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

      output(f_it->second.body, f_it->first, out);
    }
  }
}

/*******************************************************************\

Function: static_analysis_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::output(
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    get_state(i_it).output(ns, out);
    out << "\n";
    #if 0
    goto_program.output_instruction(ns, identifier, out, i_it);
    out << "\n";
    #endif
  }
}

/*******************************************************************\

Function: static_analysis_baset::generate_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::generate_states(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(f_it, goto_functions)
    generate_states(f_it->second.body);
}

/*******************************************************************\

Function: static_analysis_baset::generate_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::generate_states(
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
    generate_state(i_it);
}

/*******************************************************************\

Function: static_analysis_baset::update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::update(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(f_it, goto_functions)
    update(f_it->second.body);
}

/*******************************************************************\

Function: static_analysis_baset::generate_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::update(
  const goto_programt &goto_program)
{
  locationt previous;
  bool first=true;

  forall_goto_program_instructions(i_it, goto_program)
  {
    // do we have it already?
    if(!has_location(i_it))
    {
      generate_state(i_it);

      if(!first)
        merge(get_state(i_it), get_state(previous), i_it);
    }

    first=false;
    previous=i_it;
  }
}

/*******************************************************************\

Function: static_analysis_baset::get_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static_analysis_baset::locationt static_analysis_baset::get_next(
  working_sett &working_set)
{
  assert(!working_set.empty());

  working_sett::iterator i=working_set.begin();
  locationt l=i->second;
  working_set.erase(i);

  return l;
}

/*******************************************************************\

Function: static_analysis_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool static_analysis_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  if(goto_program.instructions.empty())
    return false;

  working_sett working_set;

  put_in_working_set(
    working_set,
    goto_program.instructions.begin());

  bool new_data=false;

  while(!working_set.empty())
  {
    ++nsteps;
    locationt l=get_next(working_set);

    if(visit(l, working_set, goto_program, goto_functions))
      new_data=true;
  }

  return new_data;
}

/*******************************************************************\

Function: static_analysis_baset::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool static_analysis_baset::visit(
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  bool new_data=false;

  statet &current=get_state(l);

  current.seen=true;

  goto_programt::const_targetst successors;

  goto_program.get_successors(l, successors);

  for(const auto &to_l : successors)
  {
    if(to_l==goto_program.instructions.end())
      continue;

    std::unique_ptr<statet> tmp_state(
      make_temporary_state(current));

    statet &new_values=*tmp_state;

    if(l->is_function_call())
    {
      // this is a big special case
      const code_function_callt &code=
        to_code_function_call(l->code);

      do_function_call_rec(
        l, to_l,
        code.function(),
        code.arguments(),
        new_values,
        goto_functions);
    }
    else
      new_values.transform(ns, l, to_l);

    statet &other=get_state(to_l);

    bool have_new_values=
      merge(other, new_values, to_l);

    if(have_new_values)
      new_data=true;

    if(have_new_values || !other.seen)
      put_in_working_set(working_set, to_l);
  }

  return new_data;
}

/*******************************************************************\

Function: static_analysis_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::do_function_call(
  locationt l_call, locationt l_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  statet &new_state)
{
  const goto_functionst::goto_functiont &goto_function=f_it->second;

  if((!goto_function.body_available()) || !should_enter_function(f_it->first))
  {
    // Per default do nothing, but a subclass might transform across the stubbed callsite.
    transform_function_stub(f_it->first,new_state,l_call,l_return);
    return;
  }

  assert(!goto_function.body.instructions.empty());

  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();

    // do the edge from the call site to the beginning of the function
    std::unique_ptr<statet> tmp_state(make_temporary_state(new_state));
    tmp_state->transform(ns, l_call, l_begin);

    statet &begin_state=get_state(l_begin);

    bool new_data=false;

    // merge the new stuff
    if(merge(begin_state, *tmp_state, l_begin))
      new_data=true;

    // do each function at least once
    if(functions_done.find(f_it->first)==
       functions_done.end())
    {
      new_data=true;
      functions_done.insert(f_it->first);
    }

    // do we need to do the fixedpoint of the body?
    if(new_data)
    {
      // recursive call
      fixedpoint(goto_function.body, goto_functions);
    }
  }

  {
    // get location at end of procedure
    locationt l_end=--goto_function.body.instructions.end();

    assert(l_end->is_end_function());

    statet &end_of_function=get_state(l_end);

    // do edge from end of function to instruction after call
    std::unique_ptr<statet> tmp_state(
      make_temporary_state(end_of_function));
    tmp_state->transform(ns, l_end, l_return);

    // propagate those -- not exceedingly precise, this is,
    // as still it contains all the state from the
    // call site
    merge(new_state, *tmp_state, l_return);
  }

  {
    // effect on current procedure (if any)
    new_state.transform(ns, l_call, l_return);
  }
}

/*******************************************************************\

Function: static_analysis_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::do_function_call_rec(
  locationt l_call, locationt l_return,
  const exprt &function,
  const exprt::operandst &arguments,
  statet &new_state,
  const goto_functionst &goto_functions)
{
  // see if we have the functions at all
  if(goto_functions.function_map.empty())
  {
    if(function.id()==ID_symbol)
    {
      auto fid=function.get(ID_identifier);
      if(!should_enter_function(fid))
        transform_function_stub(function.get(ID_identifier),new_state,l_call,l_return);
    }
    return;
  }

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=function.get(ID_identifier);

    if(ignore_recursion)
    {
      if(recursion_set.find(identifier)!=recursion_set.end())
      {
        // recursion detected!
        return;
      }
      else
        recursion_set.insert(identifier);
    }
    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);

    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);

    do_function_call(
      l_call, l_return,
      goto_functions,
      it,
      arguments,
      new_state);

    if(ignore_recursion)
      recursion_set.erase(identifier);
  }
  else if(function.id()==ID_if)
  {
    if(function.operands().size()!=3)
      throw "if takes three arguments";

    std::unique_ptr<statet> n2(make_temporary_state(new_state));

    do_function_call_rec(
      l_call, l_return,
      function.op1(),
      arguments,
      new_state,
      goto_functions);

    do_function_call_rec(
      l_call, l_return,
      function.op2(),
      arguments,
      *n2,
      goto_functions);

    merge(new_state, *n2, l_return);
  }
  else if(function.id()==ID_dereference)
  {
    // get value set
    std::list<exprt> values;
    get_reference_set(l_call, function, values);

    std::unique_ptr<statet> state_from(make_temporary_state(new_state));

    // now call all of these
    for(const auto &value : values)
    {
      if(value.id()==ID_object_descriptor)
      {
        const object_descriptor_exprt &o=to_object_descriptor_expr(value);
        std::unique_ptr<statet> n2(make_temporary_state(new_state));
        do_function_call_rec(
          l_call, l_return, o.object(), arguments, *n2, goto_functions);
        merge(new_state, *n2, l_return);
      }
    }
  }
  else if(function.id()=="NULL-object" ||
          function.id()==ID_integer_address)
  {
    // ignore, can't be a function
  }
  else if(function.id()==ID_member || function.id()==ID_index)
  {
    // ignore, can't be a function
  }
  else if(function.id()=="builtin-function")
  {
    // ignore, someone else needs to worry about this
  }
  else
  {
    throw "unexpected function_call argument: "+
      function.id_string();
  }
}

/*******************************************************************\

Function: static_analysis_baset::sequential_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::sequential_fixedpoint(
  const goto_functionst &goto_functions)
{
  // do each function at least once

  forall_goto_functions(it, goto_functions)
    if(functions_done.insert(it->first).second)
      fixedpoint(it->second.body, goto_functions);
}

/*******************************************************************\

Function: static_analysis_baset::concurrent_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysis_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions)
{
  sequential_fixedpoint(goto_functions);

  is_threadedt is_threaded(goto_functions);

  // construct an initial shared state collecting the results of all
  // functions
  goto_programt tmp;
  tmp.add_instruction();
  goto_programt::const_targett sh_target=tmp.instructions.begin();
  generate_state(sh_target);
  statet &shared_state=get_state(sh_target);

  typedef std::list<std::pair<goto_programt const*,
                              goto_programt::const_targett> > thread_wlt;
  thread_wlt thread_wl;

  forall_goto_functions(it, goto_functions)
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(is_threaded(t_it))
      {
        thread_wl.push_back(std::make_pair(&(it->second.body), t_it));

        goto_programt::const_targett l_end=
          it->second.body.instructions.end();
        --l_end;

        const statet &end_state=get_state(l_end);
        merge_shared(shared_state, end_state, sh_target);
      }
    }

  // new feed in the shared state into all concurrently executing
  // functions, and iterate until the shared state stabilizes
  bool new_shared=true;
  while(new_shared)
  {
    new_shared=false;

    for(const auto &thread : thread_wl)
    {
      working_sett working_set;
      put_in_working_set(working_set, thread.second);

      statet &begin_state=get_state(thread.second);
      merge(begin_state, shared_state, thread.second);

      while(!working_set.empty())
      {
        goto_programt::const_targett l=get_next(working_set);

        visit(l, working_set, *thread.first, goto_functions);

        // the underlying domain must make sure that the final state
        // carries all possible values; otherwise we would need to
        // merge over each and every state
        if(l->is_end_function())
        {
          statet &end_state=get_state(l);
          new_shared|=merge_shared(shared_state, end_state, sh_target);
        }
      }
    }
  }
}
