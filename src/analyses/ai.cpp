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
  const namespacet &ns,
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
    #if 0
    goto_program.output_instruction(ns, identifier, out, i_it);
    out << "\n";
    #endif
  }
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function)
{
  initialize(goto_function.body);
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it);
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    initialize(it->second);
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
  if(goto_program.instructions.empty())
    return false;
  
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
  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  if(!goto_function.body_available)
    return false; // do nothing, no change
    
  assert(!goto_function.body.instructions.empty());
  
  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    
    // do the edge from the call site to the beginning of the function
    std::auto_ptr<statet> state(make_temporary_state(get_state(l_call)));

    state->transform(l_call, l_begin, *this, ns);
    
    // merge the new stuff
    if(merge(*state, l_call, l_begin))
    {
      // also do the fixedpoint of the body via a recursive call
      fixedpoint(goto_function.body, goto_functions, ns);
    }
  }

  {
    // get location at end of the procedure we have called
    locationt l_end=--goto_function.body.instructions.end();
    assert(l_end->is_end_function());

    // do edge from end of function to instruction after call
    locationt l_next=l_call;
    l_next++;

    std::auto_ptr<statet> state(make_temporary_state(get_state(l_end)));

    state->transform(l_end, l_next, *this, ns);

    // Propagate those -- not exceedingly precise, this is.
    return merge(*state, l_end, l_next);
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
      throw "if takes three arguments";
    
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

Function: ai_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::fixedpoint(
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
