/*******************************************************************\

Module: Flow Insensitive Static Analysis

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Flow Insensitive Static Analysis

#include "flow_insensitive_analysis.h"

#include <cassert>

#include <util/expr_util.h>
#include <util/std_code.h>
#include <util/std_expr.h>

exprt flow_insensitive_abstract_domain_baset::get_guard(
  locationt from,
  locationt to) const
{
  if(!from->is_goto())
    return true_exprt();

  locationt next=from;
  next++;

  if(next==to)
    return boolean_negate(from->guard);

  return from->guard;
}

exprt flow_insensitive_abstract_domain_baset::get_return_lhs(locationt to) const
{
  // get predecessor of "to"
  to--;

  if(to->is_end_function())
    return static_cast<const exprt &>(get_nil_irep());

  // must be the function call
  return to_code_function_call(to->code).lhs();
}

void flow_insensitive_analysis_baset::operator()(
  const goto_functionst &goto_functions)
{
  initialize(goto_functions);
  fixedpoint(goto_functions);
}

void flow_insensitive_analysis_baset::operator()(
  const goto_programt &goto_program)
{
  initialize(goto_program);
  goto_functionst goto_functions;
  fixedpoint(goto_program, goto_functions);
}

void flow_insensitive_analysis_baset::output(
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  forall_goto_functions(f_it, goto_functions)
  {
    out << "////\n" << "//// Function: " << f_it->first << "\n////\n\n";

    output(f_it->second.body, f_it->first, out);
  }
}

void flow_insensitive_analysis_baset::output(
  const goto_programt &,
  const irep_idt &,
  std::ostream &out) const
{
  get_state().output(ns, out);
}

flow_insensitive_analysis_baset::locationt
flow_insensitive_analysis_baset::get_next(
  working_sett &working_set)
{
  assert(!working_set.empty());

//  working_sett::iterator i=working_set.begin();
//  locationt l=i->second;
//  working_set.erase(i);

//  pop_heap(working_set.begin(), working_set.end());
  locationt l=working_set.top();
  working_set.pop();

  return l;
}

bool flow_insensitive_analysis_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  if(goto_program.instructions.empty())
    return false;

  working_sett working_set;

//  make_heap(working_set.begin(), working_set.end());

  put_in_working_set(
    working_set,
    goto_program.instructions.begin());

  bool new_data=false;

  while(!working_set.empty())
  {
    locationt l=get_next(working_set);

    if(visit(l, working_set, goto_program, goto_functions))
      new_data=true;
  }

  return new_data;
}

bool flow_insensitive_analysis_baset::visit(
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  bool new_data=false;

  #if 0
  std::cout << "Visiting: " << l->function << " " <<
    l->location_number << '\n';
  #endif

  seen_locations.insert(l);
  if(statistics.find(l)==statistics.end())
    statistics[l]=1;
  else
    statistics[l]++;

  for(const auto &to_l : goto_program.get_successors(l))
  {
    if(to_l==goto_program.instructions.end())
      continue;

    bool changed=false;

    if(l->is_function_call())
    {
      // this is a big special case
      const code_function_callt &code = to_code_function_call(l->code);

      changed=
        do_function_call_rec(
          l,
          code.function(),
          code.arguments(),
          get_state(),
          goto_functions);
    }
    else
      changed = get_state().transform(ns, l, to_l);

    if(changed || !seen(to_l))
    {
      new_data=true;
      put_in_working_set(working_set, to_l);
    }
  }

//  if (id2string(l->function).find("debug")!=std::string::npos)
//    std::cout << l->function << '\n'; //=="messages::debug")

//  {
//    static unsigned state_cntr=0;
//    std::string s("pastate"); s += std::to_string(state_cntr);
//    std::ofstream f(s.c_str());
//    goto_program.output_instruction(ns, "", f, l);
//    f << '\n';
//    get_state().output(ns, f);
//    f.close();
//    state_cntr++;
//  }

  return new_data;
}

bool flow_insensitive_analysis_baset::do_function_call(
  locationt l_call,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &,
  statet &state)
{
  const goto_functionst::goto_functiont &goto_function=f_it->second;

  if(!goto_function.body_available())
  {
    const code_function_callt &code = to_code_function_call(l_call->code);

    goto_programt temp;

    exprt rhs =
      side_effect_expr_nondett(code.lhs().type(), l_call->source_location);

    goto_programt::targett r=temp.add_instruction();
    r->make_return();
    r->code=code_returnt(rhs);
    r->function=f_it->first;
    r->location_number=0;

    goto_programt::targett t=temp.add_instruction(END_FUNCTION);
    t->code.set(ID_identifier, code.function());
    t->function=f_it->first;
    t->location_number=1;

    locationt l_next=l_call; l_next++;
    bool new_data=state.transform(ns, l_call, r);
    new_data = state.transform(ns, r, t) || new_data;
    new_data = state.transform(ns, t, l_next) || new_data;

    return new_data;
  }

  assert(!goto_function.body.instructions.empty());

  bool new_data=false;

  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();

    DATA_INVARIANT(
      l_begin->function == f_it->first, "function names have to match");

    // do the edge from the call site to the beginning of the function
    new_data=state.transform(ns, l_call, l_begin);

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
      new_data=true; // could be reset by fixedpoint
    }
  }

  {
    // get location at end of procedure
    locationt l_end=--goto_function.body.instructions.end();

    assert(l_end->is_end_function());

    // do edge from end of function to instruction after call
    locationt l_next=l_call;
    l_next++;
    new_data = state.transform(ns, l_end, l_next) || new_data;
  }

  return new_data;
}

bool flow_insensitive_analysis_baset::do_function_call_rec(
  locationt l_call,
  const exprt &function,
  const exprt::operandst &arguments,
  statet &state,
  const goto_functionst &goto_functions)
{
  bool new_data = false;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(function).get_identifier();

    if(recursion_set.find(identifier)!=recursion_set.end())
    {
      // recursion detected!
      return false;
    }
    else
      recursion_set.insert(identifier);

    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);

    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);

    new_data =
      do_function_call(
        l_call,
        goto_functions,
        it,
        arguments,
        state);

    recursion_set.erase(identifier);
  }
  else if(function.id()==ID_if)
  {
    const auto &if_expr = to_if_expr(function);

    new_data = do_function_call_rec(
      l_call, if_expr.true_case(), arguments, state, goto_functions);

    new_data =
      do_function_call_rec(
        l_call, if_expr.false_case(), arguments, state, goto_functions) ||
      new_data;
  }
  else if(function.id()==ID_dereference)
  {
    // get value set
    expr_sett values;

    get_reference_set(function, values);

    // now call all of these
    for(const auto &v : values)
    {
      if(v.id()==ID_object_descriptor)
      {
        const object_descriptor_exprt &o=to_object_descriptor_expr(v);

        // ... but only if they are actually functions.
        goto_functionst::function_mapt::const_iterator it=
          goto_functions.function_map.find(o.object().get(ID_identifier));

        if(it!=goto_functions.function_map.end())
        {
          new_data =
            do_function_call_rec(
              l_call,
              o.object(),
              arguments,
              state,
              goto_functions) || new_data;
        }
      }
    }
  }
  else if(function.id() == ID_null_object)
  {
    // ignore, can't be a function
  }
  else if(function.id()==ID_member || function.id()==ID_index)
  {
    // ignore, can't be a function
  }
  else if(function.id()=="builtin-function")
  {
    // ignore
  }
  else
  {
    throw "unexpected function_call argument: "+
      function.id_string();
  }
  return new_data;
}

void flow_insensitive_analysis_baset::fixedpoint(
  const goto_functionst &goto_functions)
{
  // do each function at least once

  forall_goto_functions(it, goto_functions)
    if(functions_done.find(it->first)==
       functions_done.end())
    {
      fixedpoint(it, goto_functions);
    }
}

bool flow_insensitive_analysis_baset::fixedpoint(
  const goto_functionst::function_mapt::const_iterator it,
  const goto_functionst &goto_functions)
{
  functions_done.insert(it->first);
  return fixedpoint(it->second.body, goto_functions);
}

void flow_insensitive_analysis_baset::update(const goto_functionst &)
{
  // no need to copy value sets around
}

void flow_insensitive_analysis_baset::update(const goto_programt &)
{
  // no need to copy value sets around
}
