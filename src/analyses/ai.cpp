/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <memory>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include "ai.h"

/*******************************************************************\

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::output(
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    if(f_it->second.body_available)
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

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::output(
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->location << "\n";

    get_state(i_it).output(ns, out);
    out << "\n";
    goto_program.output_instruction(ns, identifier, out, i_it);
    out << "\n";
  }
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
    locationt l=get_next(working_set);
    
    if(visit(l, working_set, goto_program, goto_functions))
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
  const goto_functionst &goto_functions)
{
  bool new_data=false;

  statet &current=get_state(l);

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

    std::auto_ptr<statet> tmp_state(
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
  
    if(have_new_values)
      put_in_working_set(working_set, to_l);
  }
  
  return new_data;
}

/*******************************************************************\

Function: ai_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::do_function_call(
  locationt l_call, locationt l_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  statet &new_state)
{
  const goto_functionst::goto_functiont &goto_function=f_it->second;

  if(!goto_function.body_available)
    return; // do nothing
    
  assert(!goto_function.body.instructions.empty());

  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    
    // do the edge from the call site to the beginning of the function
    new_state.transform(ns, l_call, l_begin);  
    
    statet &begin_state=get_state(l_begin);

    bool new_data=false;

    // merge the new stuff
    if(merge(begin_state, new_state, l_begin))
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
    locationt l_next=l_call;
    l_next++;
    end_of_function.transform(ns, l_end, l_next);

    // propagate those -- not exceedingly precise, this is,
    // as still it contains all the state from the
    // call site
    merge(new_state, end_of_function, l_end);
  }
}    

/*******************************************************************\

Function: ai_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::do_function_call_rec(
  locationt l_call, locationt l_return,
  const exprt &function,
  const exprt::operandst &arguments,
  statet &new_state,
  const goto_functionst &goto_functions)
{
  // see if we have the functions at all
  if(goto_functions.function_map.empty())
    return;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=function.get(ID_identifier);
    
    if(recursion_set.find(identifier)!=recursion_set.end())
    {
      // recursion detected!
      return;
    }
    else
      recursion_set.insert(identifier);
      
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
    
    recursion_set.erase(identifier);
  }
  else if(function.id()==ID_if)
  {
    if(function.operands().size()!=3)
      throw "if takes three arguments";
    
    std::auto_ptr<statet> n2(make_temporary_state(new_state));
    
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
}

/*******************************************************************\

Function: ai_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::fixedpoint(
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

Function: ai_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::fixedpoint(
  const goto_functionst::function_mapt::const_iterator it,
  const goto_functionst &goto_functions)
{
  functions_done.insert(it->first);
  return fixedpoint(it->second.body, goto_functions);
}
