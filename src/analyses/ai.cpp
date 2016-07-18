/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <memory>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include "is_threaded.h"
#include "which_threads.h"

#include "ai.h"

/*******************************************************************\

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
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

/*******************************************************************\

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

    find_state(i_it).output(out, *this, ns);
    out << "\n";
    #if 1
    goto_program.output_instruction(ns, identifier, out, i_it);
    out << "\n";
    #endif
  }
}

/*******************************************************************\

Function: ai_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'
  
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());
    
#if 0
  std::cout << "entry state: " << goto_functions.entry_point() << std::endl;
#endif
    
  if(f_it!=goto_functions.function_map.end())
    entry_state(f_it->second.body);
}

/*******************************************************************\

Function: ai_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point,
  // and we make that 'top'.
  get_state(goto_program.instructions.begin()).make_top();  
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function,
			  const namespacet &ns)
{
  initialize(goto_function.body, ns);
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_programt &goto_program,
			  const namespacet &ns)
{
  // we mark everything as unreachable as starting point

  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it).make_bottom();
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst &goto_functions,
			  const namespacet &ns)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    initialize(it->second, ns);
}

/*******************************************************************\

Function: ai_baset::get_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ai_baset::locationt ai_baset::get_next(
  working_sett &working_set)
{
  assert(!working_set.empty());
  
  working_sett::iterator i=working_set.begin();
  locationt l=i->second;
  working_set.erase(i);
    
  return l;
}

/*******************************************************************\

Function: ai_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  working_sett working_set;

  // We will put all locations at least once into the working set.
  forall_goto_program_instructions(i_it, goto_program)
    put_in_working_set(working_set, i_it);
    
  bool new_data=false;

  while(!working_set.empty())
  {
    locationt l=get_next(working_set);
    
    if(visit(l, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

/*******************************************************************\

Function: ai_baset::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::visit(
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;

  statet &current=get_state(l);

#if 0
  std::cout << std::endl << "VISIT: " << std::endl;
  goto_program.output_instruction(ns, "", std::cout, l);
  current.output(std::cout, *this, ns);
  std::cout << std::endl;
#endif

  goto_programt::const_targetst successors;

  goto_program.get_successors(l, successors);

  for(goto_programt::const_targetst::const_iterator
      it=successors.begin();
      it!=successors.end();
      it++)
  {
    locationt to_l=*it;

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
          l, to_l,
          code.function(),
          code.arguments(),
          goto_functions, ns))
        have_new_values=true;
    }
    else
    {
      // initialize state, if necessary
      get_state(to_l);

      new_values.transform(l, to_l, *this, ns);
    
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

/*******************************************************************\

Function: ai_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::do_function_call(
  locationt l_call, locationt l_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  // initialize state, if necessary
  get_state(l_return);

  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  if(!goto_function.body_available())
  {
    // if we don't have a body, we just do an edige call -> return
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(l_call, l_return, *this, ns);

    return merge(*tmp_state, l_call, l_return);
  }
    
  assert(!goto_function.body.instructions.empty());

  // This is the edge from call site to function head.
    
  {
#if 0
    std::cout << std::endl << "CALL: " << f_it->first << std::endl;
    std::cout << "call state: " << std::endl;
    get_state(l_call).output(std::cout, *this, ns);
    std::cout << std::endl;
#endif

    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    // initialize state, if necessary
    get_state(l_begin);
    
    // do the edge from the call site to the beginning of the function
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(l_call, l_begin, *this, ns);

    bool new_data=false;

    // merge the new stuff
    if(merge(*tmp_state, l_call, l_begin))
      new_data=true;

#if 0
    std::cout << "begin state: " << std::endl;
    get_state(l_begin).output(std::cout, *this, ns);
    std::cout << std::endl;
#endif

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(goto_function.body, goto_functions, ns);
  }

  // This is the edge from function end to return site.

  {
    // get location at end of the procedure we have called
    locationt l_end=--goto_function.body.instructions.end();
    assert(l_end->is_end_function());

#if 0
    std::cout << "end state: " << std::endl;
    get_state(l_end).output(std::cout, *this, ns);
    std::cout << std::endl;
#endif

    // do edge from end of function to instruction after call
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_end)));
    tmp_state->transform(l_end, l_return, *this, ns);

    // Propagate those
    bool changed = merge(*tmp_state, l_end, l_return);

#if 0
    std::cout << "return state: " << std::endl;
    get_state(l_return).output(std::cout, *this, ns);
    std::cout << std::endl;
#endif

    return changed;
  }
}    

/*******************************************************************\

Function: ai_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::do_function_call_rec(
  locationt l_call, locationt l_return,
  const exprt &function,
  const exprt::operandst &arguments,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  assert(!goto_functions.function_map.empty());
  
  bool new_data=false;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=function.get(ID_identifier);
    
    if(recursion_set.find(identifier)!=recursion_set.end())
    {
      // recursion detected!
      return new_data;
    }
    else
      recursion_set.insert(identifier);
      
    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);
      
    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);
    
    new_data=do_function_call(
      l_call, l_return,
      goto_functions,
      it,
      arguments,
      ns);
    
    recursion_set.erase(identifier);
  }
  else if(function.id()==ID_if)
  {
    if(function.operands().size()!=3)
      throw "if has three operands";
    
    bool new_data1=
      do_function_call_rec(
        l_call, l_return,
        function.op1(),
        arguments,
        goto_functions,
        ns);

    bool new_data2=
      do_function_call_rec(
        l_call, l_return,
        function.op2(),
        arguments,
        goto_functions,
        ns);

    if(new_data1 || new_data2)
      new_data=true;
  }
  else if(function.id()==ID_dereference)
  {
    // We can't really do this here -- we rely on
    // these being removed by some previous analysis.
  }
  else if(function.id()=="NULL-object")
  {
    // ignore, can't be a function
  }
  else if(function.id()==ID_member || function.id()==ID_index)
  {
    // ignore, can't be a function
  }
  else
  {
    throw "unexpected function_call argument: "+
      function.id_string();
  }
  
  return new_data;
}

/*******************************************************************\

Function: ai_baset::sequential_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::sequential_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  // do each function at least once

  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    fixedpoint(it->second.body, goto_functions, ns);
}

/*******************************************************************\

Function: ai_baset::concurrent_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  sequential_fixedpoint(goto_functions, ns);

//  is_threadedt is_threaded(goto_functions); //TODO: does not work
  which_threadst which_threads(goto_functions);

  // construct an initial shared state collecting the results of all
  // functions
  goto_programt tmp;
  tmp.add_instruction();
  goto_programt::const_targett sh_target=tmp.instructions.begin();
  statet &shared_state=get_state(sh_target);

  typedef std::list<std::pair<goto_programt const*,
                              goto_programt::const_targett> > thread_wlt;
  thread_wlt thread_wl;

#if 0 //TODO: observation:
      //  is_threaded on individual instructions does not seem 
      //  to take into account all dependencies
  forall_goto_functions(it, goto_functions)
  {
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(which_threads.is_threaded(t_it))
      {
        thread_wl.push_back(std::make_pair(&(it->second.body), t_it));

        const statet &state=get_state(t_it);
        merge_shared(state, t_it, sh_target, ns);
      }      
      }
    }
#else //this iterates over the whole function that contains is_threaded
  forall_goto_functions(it, goto_functions)
  {
    bool is_threaded = false;
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(which_threads.is_threaded(t_it))
      {
        is_threaded = true;
        break;
      }
    }
    if(is_threaded)
    {
      thread_wl.push_back(std::make_pair(&(it->second.body), 
        it->second.body.instructions.begin()));
      forall_goto_program_instructions(t_it, it->second.body)
      {
        const statet &state=get_state(t_it);
#if 0
	std::cout << "add to shared state: " << std::endl;
	state.output(std::cout, *this, ns);
#endif
        merge_shared(state, t_it, sh_target, ns);
      }      
    }
  }
#endif
#if 1
  std::cout << "shared state: " << std::endl;
  shared_state.output(std::cout, *this, ns);
  std::cout << std::endl;
#endif

  // now feed in the shared state into all concurrently executing
  // functions, and iterate until the shared state stabilizes
  bool new_shared=true;
  while(new_shared)
  {
    new_shared=false;

    for(thread_wlt::const_iterator it=thread_wl.begin();
        it!=thread_wl.end();
        ++it)
    {
      working_sett working_set;
      put_in_working_set(working_set, it->second);

      merge(shared_state, sh_target, it->second);

#if 0
      statet &begin_state=get_state(it->second);
      std::cout << "begin state: " << it->second->location_number << std::endl;
      begin_state.output(std::cout, *this, ns);
      std::cout << std::endl;
#endif

      while(!working_set.empty())
      {
        goto_programt::const_targett l=get_next(working_set);

        visit(l, working_set, *(it->first), goto_functions, ns);

        statet &state=get_state(l);
        new_shared|=merge_shared(state, l, sh_target, ns);
      }
    }
  }
}

