/*******************************************************************\

Module: Abstract Interpretation (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#include <cassert>
#include <memory>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include "ai_cs.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: print function pointer map

\*******************************************************************/

std::ostream &operator<<(std::ostream &out, const ai_cs_baset::fp_mapt &fp_map)
{
  out << "{\n";
  for (ai_cs_baset::fp_mapt::const_iterator it=fp_map.begin();
       it!=fp_map.end(); ++it)
  {
    std::string var=id2string(it->first);
    std::string tgt=id2string(it->second);
    out << var << " -> " << tgt << "\n";
  }
  out << "}";
  return out;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: print place

\*******************************************************************/

std::ostream &operator<<(std::ostream &out, const ai_cs_baset::placet &place)
{
  out << "(";
  out << place.first;
  out << ", ";
  out << place.second->location_number;
  out << ")";
  return out;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: print set of places

\*******************************************************************/

std::ostream &operator<<(std::ostream &out, const ai_cs_baset::placest &places)
{
  out << "{";
  bool first = true;
  for(const ai_cs_baset::placet &place : places)
  {
    if(!first) out << ", ";
    else first = false;
    out << place;
  }
  out << "}";
  return out;
}

/*******************************************************************\

Function: ai_cs_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  std::ostream &out) const
{
  assert(!goto_program.instructions.empty());
  locationt start=goto_program.instructions.begin();

  std::set<ai_cs_stackt> stacks;
  find_stacks(start, stacks);

  if(stacks.empty())
  {
    out << "<no stacks for function entry point>";
    return;
  }
  for(const ai_cs_stackt stack : stacks)
  {
    out << "++++ " << stack << "\n\n";
    output(ns, goto_program, "", stack, out);
  }
}

/*******************************************************************\

Function: ai_cs_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    irep_idt id=f_it->first;
    const goto_functiont &goto_function=f_it->second;

    if(goto_function.body_available())
    {
      const goto_programt &goto_program=goto_function.body;

      out << "////\n";
      out << "//// Function: " << id << "\n";
      out << "////\n";
      out << "\n";

      // find all contexts
      assert(!goto_program.instructions.empty());
      locationt start=goto_function.body.instructions.begin();
      std::set<ai_cs_stackt> stacks;
      find_stacks(start, stacks);

      if(stacks.empty())
      {
        out << "<no stacks for function entry point>\n\n";
        continue;
      }

      for (ai_cs_stackt stack : stacks)
      {
        out << "++++ " << stack << "\n\n";

        // function pointer state
        fp_state_mapt::const_iterator it=fp_state_map.find(stack);
        if (it!=fp_state_map.end())
          out << it->second << "\n";
        else
          out << "{}\n\n";

        // parametrising state
        output(ns, goto_program, f_it->first, stack, out);
        out << "\n\n";
      }
    }
  }
}

/*******************************************************************\

Function: ai_cs_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  const ai_cs_stackt &stack,
  std::ostream &out) const
{
  assert(!goto_program.instructions.empty());

  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n\n";

    placet place(stack, i_it);
    if(!has(place))
    {
      out << "<no information for place>";
    }
    else
    {
      const statet &state=find_state(stack, i_it);
      state.output(out, *this, ns);
    }

    #if 1
    out << "\n\n";
    goto_program.output_instruction(ns, identifier, out, i_it);
    #endif
  }
}

/*******************************************************************\

Function: ai_cs_baset::get_function_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::pair<bool, const irep_idt> ai_cs_baset::get_function_identifier(
  const ai_cs_stackt &stack,
  const exprt &expr,
  const goto_functionst &goto_functions)
{
  if(expr.id()==ID_symbol)
  {
    irep_idt identifier=misc::get_identifier(expr);
    assert(!identifier.empty());

    if(goto_functions.function_map.find(identifier)
       !=goto_functions.function_map.end())
    {
      // resolved directly
      return std::make_pair(true, identifier);
    }

    fp_state_mapt::const_iterator it=fp_state_map.find(stack);
    if (it!=fp_state_map.end())
    {
      const fp_mapt &fp_map=it->second;
      fp_mapt::const_iterator m_it=fp_map.find(identifier);
      if (m_it!=fp_map.end())
      {
        // resolved via function pointer
        return std::make_pair(false, m_it->second);
      }
    }
  }
  else if(expr.id()==ID_typecast || expr.id()==ID_address_of)
  {
    return get_function_identifier(stack, expr.op0(), goto_functions);
  }
  else if(expr.id()==ID_constant)
  {
    // can't be a function
  }
  else if(expr.id()==ID_member ||
          expr.id()==ID_dereference ||
          expr.id()==ID_index ||
          expr.id()==ID_if)
  {
    // we can't handle:
    // - field accesses
    // - dereferences of pointers to function pointers
    // - array accesses
    // - if-else expressions
  }
  else
  {
    chk(false, expr.pretty());
  }

  return std::make_pair(false, irep_idt());
}

/*******************************************************************\

Function: ai_cs_baset::add_function_pointer_mapping

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// add mapping for one argument-parameter pair
void ai_cs_baset::add_function_pointer_mapping(
  const ai_cs_stackt &old_stack,
  const ai_cs_stackt &new_stack,
  unsigned caller_arg_idx,
  unsigned callee_par_idx,
  const exprt::operandst &arguments, // arguments of call
  const goto_functiont &goto_function, // called function
  const goto_functionst &goto_functions)
{
  assert(caller_arg_idx < arguments.size());
  assert(is_function_pointer(arguments[caller_arg_idx]));

  const exprt &arg=arguments[caller_arg_idx];
  std::pair<bool, const irep_idt> p
    =get_function_identifier(old_stack, arg, goto_functions);

  const irep_idt tgt=p.second;

  if (tgt.empty())
    return;

  std::vector<irep_idt> pars=goto_function.type.parameter_identifiers();
  assert(callee_par_idx < pars.size());

  fp_mapt &fp_map=fp_state_map[new_stack];
  fp_map.insert(std::make_pair(pars[callee_par_idx], tgt));
}

/*******************************************************************\

Function: ai_cs_baset::update_function_pointer_mappings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::update_function_pointer_mappings(
  const ai_cs_stackt &old_stack,
  const ai_cs_stackt &new_stack,
  const exprt::operandst &arguments,
  const goto_functiont &goto_function, // called function
  const goto_functionst &goto_functions)
{
  std::vector<irep_idt> pars=goto_function.type.parameter_identifiers();

  if(arguments.size()!=pars.size()) // we ignore vararg functions
    return;

  unsigned n=arguments.size();
  for (unsigned i=0; i<n; i++)
  {
    if (!is_function_pointer(arguments[i]))
      continue;

    add_function_pointer_mapping(
      old_stack,
      new_stack,
      i,
      i,
      arguments,
      goto_function,  // called function
      goto_functions);
  }
}

/*******************************************************************\

Function: ai_cs_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if (f_it==goto_functions.function_map.end())
    throw "no entry point";
  entry_state(f_it->second.body);
}

/*******************************************************************\

Function: ai_cs_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point. The
  // call stack is empty. We make that 'top'.
  statet &state=get_state(ai_cs_stackt(), goto_program.instructions.begin());
  state.make_top();
}

/*******************************************************************\

Function: ai_cs_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::initialize(
  const goto_functiont &goto_function,
  const namespacet &ns)
{
  initialize(goto_function.body, ns);
}

/*******************************************************************\

Function: ai_cs_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::initialize(
  const goto_programt &goto_program,
  const namespacet &ns)
{

}

/*******************************************************************\

Function: ai_cs_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::initialize(const goto_functionst &goto_functions,
			     const namespacet &ns)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    initialize(it->second, ns);
}

/*******************************************************************\

Function: ai_cs_baset::get_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ai_cs_baset::placet ai_cs_baset::get_next(
  working_sett &working_set)
{
  assert(!working_set.empty());
  
  placet element=working_set.front();
  working_set.pop();
    
  return element;
}

/*******************************************************************\

Function: ai_cs_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const ai_cs_stackt &stack,
  const namespacet &ns)
{
  working_sett working_set;
    
  // We put only the starting location and the given stack into the
  // working set at the beginning
  put_in_working_set(working_set, goto_program.instructions.begin(), stack);

  bool new_data=false;

  while(!working_set.empty())
  {
    placet element=get_next(working_set);
    const ai_cs_stackt &stack = element.first;
    locationt l = element.second;

    if(visit(l, stack, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

/*******************************************************************\

Function: ai_cs_baset::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_baset::visit(
  locationt l,
  const ai_cs_stackt &stack,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;
  set_seen(stack, l);

  // creates states if necessary
  const statet &current=get_const_state(stack, l);

  goto_programt::const_targetst successors;
  goto_program.get_successors(l, successors);
  assert(!l->is_function_call() || successors.size()==1);

  for(goto_programt::const_targetst::const_iterator it=successors.begin();
      it!=successors.end();
      it++)
  {
    locationt to_l=*it;
    assert(to_l!=goto_program.instructions.end());
    
    bool have_new_values=false;

    if(l->is_function_call() &&
       !goto_functions.function_map.empty())
    {
      // this is a big special case
      // can be a regular function call or invocation of create_thread

      const code_function_callt &code=to_code_function_call(l->code);

      if(do_function_call_rec(
          l,
          to_l, // return location
          stack,
          code.function(), // function identifier or pointer expression
          code.arguments(), // arguments as expression vector
          goto_functions,
          ns))
      {
        have_new_values=true;
      }
    }
    else
    {
      // new state
      std::unique_ptr<statet> tmp_state(make_temporary_state(current));
      statet &new_values=*tmp_state;

      // initialize state, if necessary
      get_const_state(stack, to_l);

      if(in_slice(l))
      {
#if 0
	std::cout << "in slice: " 
		  << l->location_number << std::endl;
#endif
        new_values.transform(l, to_l, stack, *this, ns);
      }
      else //treat as skip
      {
#if 0
	std::cout << "not in slice: " 
		  << l->location_number << std::endl;
#endif
        new_values=current;
      }
    
      if(merge(new_values, l, to_l, stack))
        have_new_values=true;
    }
  
    if(have_new_values || !seen(stack, to_l))
    {
      new_data=true;
      put_in_working_set(working_set, to_l, stack);
    }
  }
  
  return new_data;
}

/*******************************************************************\

Function: ai_cs_baset::do_thread_create

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::do_thread_create(
  locationt l_call,
  locationt l_return,
  const ai_cs_stackt &stack, // stack before this call
  const goto_functionst &goto_functions,
  const exprt::operandst &arguments, // arguments to pthread_create
  const namespacet &ns)
{
  num_thread_create++;

  // get identifier of the caller
  const irep_idt &caller=l_call->function;
  assert(!caller.empty());

  unsigned thread_idx=config.ansi_c.create_thread_arg_no_of_function;
  unsigned thread_arg_idx=config.ansi_c.create_thread_arg_no_of_arg;

  // get created thread function
  assert(thread_idx<arguments.size());

  irep_idt thread;
  const exprt &created_thread=arguments[thread_idx];

  std::pair<bool, const irep_idt> p
    =get_function_identifier(stack, created_thread, goto_functions);

  thread=p.second;

  if(!thread.empty())
  {
    if(p.first)
      num_resolved_direct++;
    else
      num_resolved_fp++;

    const goto_functiont &goto_function=
      get_goto_function(thread, goto_functions); // always succeeds

    if (goto_function.body_available())
    {
      if(recursion_set.find(thread)!=recursion_set.end())
      {
        // recursion detected!
        has_recursion=true;
        return;
      }
      else
      {
        recursion_set.insert(thread);
      }

      // copy and update stack
      ai_cs_stackt new_stack=stack;
#if 1
      new_stack.frames.push_back(
        std::make_tuple(caller, l_call, ai_cs_stackt::SE_THREAD_CREATE));
      assert(new_stack.frames.size()==stack.frames.size()+1);
#endif

      // get the state at the beginning of the thread
      locationt l_begin=goto_function.body.instructions.begin();
      // initialize state, if necessary
      get_const_state(new_stack, l_begin);

      if(is_function_pointer(arguments[thread_arg_idx]))
      {
        add_function_pointer_mapping(
          stack,
          new_stack,
          thread_arg_idx,
          0,
          arguments,
          goto_function,  // called function
          goto_functions);
      }

      // do the edge from the creation site to the beginning of the function
      std::unique_ptr<statet> new_state(
        make_temporary_state(get_const_state(stack, l_call)));
      new_state->transform(l_call, l_begin, new_stack, *this, ns);

      bool new_data;
      new_data=merge(*new_state, l_call, l_begin, new_stack);

      // do we need to do/re-do the fixedpoint of the body?
      if(new_data || !seen(new_stack, l_begin))
        fixedpoint(goto_function.body, goto_functions, new_stack, ns);

      recursion_set.erase(thread);
    }
  }
}

/*******************************************************************\

Function: ai_cs_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_baset::do_function_call(
  locationt l_call,
  locationt l_return,
  const ai_cs_stackt &stack, // stack before this call
  const goto_functionst &goto_functions,
  const irep_idt &identifier, // identifier of the called function
  const exprt::operandst &arguments, // function call arguments
  const namespacet &ns)
{
  assert(l_call->is_function_call());

  // get identifier of the caller
  const irep_idt &caller=l_call->function;
  assert(!caller.empty());

  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(identifier);
  if(it==goto_functions.function_map.end())
    throw "failed to find function "+id2string(identifier);

  const goto_functiont &goto_function=it->second;

  // initialize state, if necessary
  get_const_state(stack, l_return);
  bool new_data;

  // handle locally
  if(!goto_function.body_available() || !in_slice(l_call))
  {
    statet *state = make_temporary_state(get_const_state(stack, l_call));
    std::unique_ptr<statet> new_state(state);
    new_state->transform(l_call, l_return, stack, *this, ns);

    new_data=merge(*new_state, l_call, l_return, stack);
  }
  else
  {
    assert(!goto_function.body.instructions.empty());

    // copy and update stack
    ai_cs_stackt new_stack=stack;
#if 1
    new_stack.frames.push_back(
      std::make_tuple(caller, l_call, ai_cs_stackt::SE_FUNCTION_CALL));
    assert(new_stack.frames.size()==stack.frames.size()+1);
#endif

    {
      // get the state at the beginning of the function
      locationt l_begin=goto_function.body.instructions.begin();
      // initialize state, if necessary
      get_const_state(new_stack, l_begin);

      update_function_pointer_mappings(
        stack,
        new_stack,
        arguments,
        goto_function, // called function
        goto_functions);

      // do the edge from the call site to the beginning of the function
      std::unique_ptr<statet> new_state(
        make_temporary_state(get_const_state(stack, l_call)));
      new_state->transform(l_call, l_begin, new_stack, *this, ns);

      // merge the new stuff
      new_data=merge(*new_state, l_call, l_begin, new_stack);

      // do we need to do/re-do the fixedpoint of the body?
      if(new_data || !seen(new_stack, l_begin))
        fixedpoint(goto_function.body, goto_functions, new_stack, ns);
    }

    {
      // get location at end of the procedure we have called
      locationt l_end=--goto_function.body.instructions.end();
      assert(l_end->is_end_function());

      // do edge from end of function to instruction after call
      std::unique_ptr<statet> new_state(
        make_temporary_state(get_const_state(new_stack, l_end)));
      new_state->transform(l_end, l_return, new_stack, *this, ns);

      new_data=merge(*new_state, l_end, l_return, stack);
    }
  }

  if (id2string(identifier)==config.ansi_c.create_thread)
  {
    // do not link to pthread_lib
    assert(!goto_function.body_available());

    do_thread_create(
      l_call,
      l_return,
      stack,
      goto_functions,
      arguments, // arguments to pthread_create
      ns);
  }

  return new_data;
}

/*******************************************************************\

Function: ai_cs_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_baset::do_function_call_rec(
  locationt l_call,
  locationt l_return,
  const ai_cs_stackt &stack,
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
    assert(!identifier.empty());

    // recursion is currently handled in an unsound way, to fix this
    // we would have to go into recursive calls until we reach a
    // fixpoint
    if(recursion_set.find(identifier)!=recursion_set.end())
    {
      // recursion detected!
      has_recursion=true;
      return new_data;
    }
    else if(id2string(identifier)!=config.ansi_c.create_thread)
    {
      recursion_set.insert(identifier);
    }
    
    new_data=do_function_call(
      l_call,
      l_return,
      stack, // current stack
      goto_functions,
      identifier, // function identifier
      arguments,
      ns);
    
    recursion_set.erase(identifier);
  }
  else if(function.id()==ID_if)
  {
    // recursively handle all possible targets
    chk(false, "error");

    if(function.operands().size()!=3)
      throw "if has != three operands";
    
    bool new_data1=
      do_function_call_rec(
        l_call,
        l_return,
        stack,
        function.op1(),
        arguments,
        goto_functions,
        ns);

    bool new_data2=
      do_function_call_rec(
        l_call,
        l_return,
        stack,
        function.op2(),
        arguments,
        goto_functions,
        ns);

    if(new_data1 || new_data2)
      new_data=true;
  }
  else if(function.id()==ID_dereference)
  {
    // ignore calls through function pointers
  }
  else if(function.id()=="NULL-object")
  {
    // ignore, can't be a function
    chk(false, "error");
  }
  else if(function.id()==ID_member || function.id()==ID_index)
  {
    // ignore, can't be a function
    chk(false, "error");
  }
  else
  {
    chk(false, "unexpected function_call argument: "+function.id_string());
  }
  
  return new_data;
}

/*******************************************************************\

Function: ai_cs_baset::sequential_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_baset::fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());
  assert(f_it!=goto_functions.function_map.end());

  // start worklist algorithm
  fixedpoint(f_it->second.body, goto_functions, ai_cs_stackt(), ns);
}
