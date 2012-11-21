/*******************************************************************\

Module: Flow Insensitive Static Analysis

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#include <assert.h>

#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>

#include "flow_insensitive_analysis.h"

//#include <fstream>
//#include <i2string.h>

/*******************************************************************\

Function: flow_insensitive_abstract_domain_baset::get_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flow_insensitive_abstract_domain_baset::get_guard(
  locationt from,
  locationt to) const
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

Function: flow_insensitive_abstract_domain_baset::get_return_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flow_insensitive_abstract_domain_baset::get_return_lhs(locationt to) const
{
  // get predecessor of "to"

  to--;

  if(to->is_end_function())
    return static_cast<const exprt &>(get_nil_irep());
  
  // must be the function call
  assert(to->is_function_call());

  const code_function_callt &code=
    to_code_function_call(to_code(to->code));
  
  return code.lhs();
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::operator()(
  const goto_functionst &goto_functions)
{
  initialize(goto_functions);
  fixedpoint(goto_functions);
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::operator()(
  const goto_programt &goto_program)
{
  initialize(goto_program);
  goto_functionst goto_functions;
  fixedpoint(goto_program, goto_functions);
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::output(
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    out << "////" << std::endl;
    out << "//// Function: " << f_it->first << std::endl;
    out << "////" << std::endl;
    out << std::endl;

    output(f_it->second.body, f_it->first, out);
  }
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::output(
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  get_state().output(ns, out);  
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::get_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

flow_insensitive_analysis_baset::locationt flow_insensitive_analysis_baset::get_next(
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

/*******************************************************************\

Function: flow_insensitive_analysis_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: flow_insensitive_analysis_baset::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool flow_insensitive_analysis_baset::visit(
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  bool new_data=false;
  
  #if 0
  std::cout << "Visiting: " << l->function << " " << 
    l->location_number << std::endl;
  #endif

  goto_programt::const_targetst successors;
  goto_program.get_successors(l, successors);
  
  seen_locations.insert(l);
  if (statistics.find(l)==statistics.end())
    statistics[l]=1;
  else
    statistics[l]++;

  for(goto_programt::const_targetst::const_iterator
      it=successors.begin();
      it!=successors.end();
      it++)
  {
    locationt to_l=*it;

    if(to_l==goto_program.instructions.end())
      continue;
      
    bool changed=false;
    
    if(l->is_function_call())
    {
      // this is a big special case
      const code_function_callt &code=
        to_code_function_call(to_code(l->code));
      
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
//    std::cout << l->function << std::endl; //=="c::messages::debug")
  
//  {
//    static unsigned state_cntr=0;
//    std::string s("pastate"); s += i2string(state_cntr);
//    std::ofstream f(s.c_str());
//    goto_program.output_instruction(ns, "", f, l);
//    f << std::endl;
//    get_state().output(ns, f);
//    f.close();
//    state_cntr++;
//  }

  return new_data;
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool flow_insensitive_analysis_baset::do_function_call(
  locationt l_call,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  statet &state)
{
  const goto_functionst::goto_functiont &goto_function=f_it->second;

	if(!goto_function.body_available)
	{
	  const code_function_callt &code = 
      to_code_function_call(to_code(l_call->code));
    
    goto_programt temp;
    
    goto_programt::targett r=temp.add_instruction();
    r->make_return();
    r->code=code_returnt();
    r->function=f_it->first;
    r->location_number=0;
    
    exprt rhs=side_effect_expr_nondett(code.lhs().type());
    r->code.move_to_operands(rhs);    
    
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

/*******************************************************************\

Function: flow_insensitive_analysis_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    const irep_idt &identifier=function.get(ID_identifier);
    
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
    {      
      std::cout << "failed to find function " << id2string(identifier) << std::endl;
      throw "failed to find function "+id2string(identifier);
    }
    
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
    if(function.operands().size()!=3)
      throw "if takes three arguments";
    
    new_data = 
      do_function_call_rec(
        l_call,
        function.op1(),
        arguments,
        state,
        goto_functions);

    new_data =
      do_function_call_rec(
        l_call,
        function.op2(),
        arguments,
        state,
        goto_functions) || new_data;
  }
  else if(function.id()==ID_dereference)
  {
    // get value set
    expr_sett values;
    
    get_reference_set(function, values);

    // now call all of these
    for(expr_sett::const_iterator it=values.begin();
        it!=values.end();
        it++)
    {
      if(it->id()==ID_object_descriptor)
      {
        const object_descriptor_exprt &o=to_object_descriptor_expr(*it);
        
        // ... but only if they are actually functions.
        goto_functionst::function_mapt::const_iterator it=
          goto_functions.function_map.find(o.object().get(ID_identifier));
        
        if (it!=goto_functions.function_map.end())
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
  else if(function.id()=="NULL-object")
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

/*******************************************************************\

Function: flow_insensitive_analysis_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::fixedpoint(
  const goto_functionst &goto_functions)
{
  // do each function at least once

  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(functions_done.find(it->first)==
       functions_done.end())
    {
      fixedpoint(it, goto_functions);
    }
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool flow_insensitive_analysis_baset::fixedpoint(
  const goto_functionst::function_mapt::const_iterator it,
  const goto_functionst &goto_functions)
{
  functions_done.insert(it->first);
  return fixedpoint(it->second.body, goto_functions);
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::update(
  const goto_functionst &goto_functions)
{
  // no need to copy value sets around
}

/*******************************************************************\

Function: flow_insensitive_analysis_baset::update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::update(
  const goto_programt &goto_program)
{
  // no need to copy value sets around
}
