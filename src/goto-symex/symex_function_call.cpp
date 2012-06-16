/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <i2string.h>
#include <cprover_prefix.h>
#include <prefix.h>
#include <arith_tools.h>
#include <base_type.h>
#include <std_expr.h>
#include <context.h>

#include <ansi-c/c_types.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::get_unwind_recursion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_symext::get_unwind_recursion(
  const irep_idt &identifier,
  unsigned unwind)
{
  return false;
}

/*******************************************************************\

Function: goto_symext::argument_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::argument_assignments(
  const irep_idt function_identifier,
  const code_typet &function_type,
  statet &state,
  const exprt::operandst &arguments)
{
  // iterates over the operands
  exprt::operandst::const_iterator it1=arguments.begin();

  // these are the types of the arguments
  const code_typet::argumentst &argument_types=function_type.arguments();

  // iterates over the types of the arguments
  for(code_typet::argumentst::const_iterator
      it2=argument_types.begin();
      it2!=argument_types.end();
      it2++)
  {
    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
      throw "function call: not enough arguments";

    const code_typet::argumentt &argument=*it2;

    // this is the type the n-th argument should be
    const typet &arg_type=argument.type();

    const irep_idt &identifier=argument.get_identifier();
    
    if(identifier==irep_idt())
      throw "no identifier for function argument";

    const symbolt &symbol=ns.lookup(identifier);
    symbol_exprt lhs=symbol_expr(symbol);

    if(it1->is_nil())
    {
      // 'nil' argument doesn't get assigned
    }
    else
    {
      exprt rhs=*it1;

      // it should be the same exact type
      if(!base_type_eq(arg_type, rhs.type(), ns))
      {
        const typet &f_arg_type=ns.follow(arg_type);
        const typet &f_rhs_type=ns.follow(rhs.type());
      
        // we are willing to do some limited conversion
        if((f_arg_type.id()==ID_signedbv ||
            f_arg_type.id()==ID_unsignedbv ||
            f_arg_type.id()==ID_bool ||
            f_arg_type.id()==ID_pointer) &&
           (f_rhs_type.id()==ID_signedbv ||
            f_rhs_type.id()==ID_unsignedbv ||
            f_rhs_type.id()==ID_bool ||
            f_rhs_type.id()==ID_pointer))
        {
          rhs.make_typecast(arg_type);
        }
        else
        {
          std::string error="function call: argument \""+
            id2string(identifier)+"\" type mismatch: got "+
            it1->type().to_string()+", expected "+
            arg_type.to_string();
          throw error;
        }
      }
      
      guardt guard;
      state.rename(lhs, ns, goto_symex_statet::L1);
      symex_assign_symbol(state, lhs, nil_exprt(), rhs, guard, VISIBLE);
    }

    it1++;
  }

  if(function_type.has_ellipsis())
  {
    // These are va_arg arguments.
    for(unsigned va_count=0; it1!=arguments.end(); it1++, va_count++)
    {
      irep_idt id=id2string(function_identifier)+"::va_arg"+i2string(va_count);
      
      // add to context
      symbolt symbol;
      symbol.name=id;
      symbol.base_name="va_arg"+i2string(va_count);
      symbol.type=it1->type();
      
      new_context.move(symbol);
      
      symbol_exprt lhs=symbol_exprt(id, it1->type());

      guardt guard;
      state.rename(lhs, ns, goto_symex_statet::L1);
      symex_assign_symbol(state, lhs, nil_exprt(), *it1, guard, VISIBLE);
    }
  }
  else if(it1!=arguments.end())
  {
    // we got too many arguments, but we will just ignore them
  }
}

/*******************************************************************\

Function: goto_symext::symex_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_function_call(
  const goto_functionst &goto_functions,
  statet &state,
  const code_function_callt &code)
{
  const exprt &function=code.function();

  if(function.id()==ID_symbol)
    symex_function_call_symbol(goto_functions, state, code);
  else if(function.id()==ID_if)
    throw "symex_function_call can't do if";
  else if(function.id()==ID_dereference)
    throw "symex_function_call can't do dereference";
  else
    throw "unexpected function for symex_function_call: "+function.id_string();
}

/*******************************************************************\

Function: goto_symext::symex_function_call_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_function_call_symbol(
  const goto_functionst &goto_functions,
  statet &state,
  const code_function_callt &code)
{
  target.location(state.guard, state.source);

  assert(code.function().id()==ID_symbol);

  const irep_idt &identifier=
    to_symbol_expr(code.function()).get_identifier();
    
  if(identifier=="c::CBMC_trace")
  {
    symex_trace(state, code);
  }
  else if(has_prefix(id2string(identifier), CPROVER_FKT_PREFIX))
  {
    symex_fkt(state, code);
  }
  else if(has_prefix(id2string(identifier), CPROVER_MACRO_PREFIX))
  {
    symex_macro(state, code);
  }
  else
    symex_function_call_code(goto_functions, state, code);
}

/*******************************************************************\

Function: goto_symext::symex_function_call_code

  Inputs:

 Outputs:

 Purpose: do function call by inlining

\*******************************************************************/

void goto_symext::symex_function_call_code(
  const goto_functionst &goto_functions,
  statet &state,
  const code_function_callt &call)
{
  const irep_idt &identifier=
    to_symbol_expr(call.function()).get_identifier();
  
  // find code in function map
  
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(identifier);

  if(it==goto_functions.function_map.end())
    throw "failed to find `"+id2string(identifier)+"' in function_map";

  const goto_functionst::goto_functiont &goto_function=it->second;
  
  unsigned &unwinding_counter=function_unwind[identifier];

  // see if it's too much
  if(get_unwind_recursion(identifier, unwinding_counter))
  {
    // these have low priority
    if(options.get_bool_option("unwinding-assertions"))
      claim(false_exprt(), "recursion unwinding assertion", 1, state);

    state.source.pc++;
    return;
  }
  
  // record the call
  target.function_call(state.guard, identifier, state.source);

  if(!goto_function.body_available)
  {
    no_body(identifier);
    
    // record the return
    target.function_return(state.guard, identifier, state.source);
  
    if(call.lhs().is_not_nil())
    {
      exprt rhs=exprt(ID_nondet_symbol, call.lhs().type());
      rhs.set(ID_identifier, "symex::"+i2string(nondet_count++));
      rhs.location()=call.location();
      state.rename(rhs, ns, goto_symex_statet::L1);
      code_assignt code(call.lhs(), rhs);
      basic_symext::symex_assign(state, to_code_assign(code)); /* TODO: clean_expr? */
    }

    state.source.pc++;
    return;
  }
  
  // read the arguments -- before the locality renaming
  exprt::operandst arguments=call.arguments();
  for(unsigned i=0; i<arguments.size(); i++)
    state.rename(arguments[i], ns);
  
  // increase unwinding counter
  unwinding_counter++;
  
  // produce a new frame
  assert(!state.call_stack.empty());
  goto_symex_statet::framet &frame=state.new_frame();
  
  // copy L1 renaming from previous frame
  frame.level1=state.previous_frame().level1;
  
  unsigned &frame_nr=function_frame[identifier];
  frame_nr++;
  
  // preserve locality of local variables
  locality(frame_nr, state, goto_function);

  // assign arguments
  argument_assignments(identifier, goto_function.type, state, arguments);

  frame.end_of_function=--goto_function.body.instructions.end();
  frame.return_value=call.lhs();
  frame.calling_location=state.source;
  frame.function_identifier=identifier;

  state.source.is_set=true;
  state.source.pc=goto_function.body.instructions.begin();
}

/*******************************************************************\

Function: goto_symext::pop_frame

  Inputs:

 Outputs:

 Purpose: pop one call frame

\*******************************************************************/

void goto_symext::pop_frame(statet &state)
{
  assert(!state.call_stack.empty());

  statet::framet &frame=state.top();

  // restore state
  state.source.pc=frame.calling_location.pc;
  
  // clear locals from L2 renaming
  for(statet::framet::local_variablest::const_iterator
      it=frame.local_variables.begin();
      it!=frame.local_variables.end();
      it++)
    state.level2.remove(*it);

  // decrease recursion unwinding counter
  if(frame.function_identifier!="")
    function_unwind[frame.function_identifier]--;
  
  state.pop_frame();
}

/*******************************************************************\

Function: goto_symext::symex_end_of_function

  Inputs:

 Outputs:

 Purpose: do function call by inlining

\*******************************************************************/

void goto_symext::symex_end_of_function(statet &state)
{
  // first record the return
  target.function_return(state.guard, state.source.pc->function, state.source);

  // then get rid of the frame
  pop_frame(state);  
}

/*******************************************************************\

Function: goto_symext::locality

  Inputs:

 Outputs:

 Purpose: preserves locality of local variables of a given
          function by applying L1 renaming to the local
          identifiers

\*******************************************************************/

void goto_symext::locality(
  unsigned frame_nr,
  statet &state,
  const goto_functionst::goto_functiont &goto_function)
{
  std::set<irep_idt> local_identifiers;
  
  get_local_identifiers(goto_function, local_identifiers);

  statet::framet &frame=state.top();

  for(std::set<irep_idt>::const_iterator
      it=local_identifiers.begin();
      it!=local_identifiers.end();
      it++)
  {
    // get L0 name
    irep_idt l0_name=state.rename(*it, ns, goto_symex_statet::L0);
    
    // do L1 renaming -- these need not be unique, as
    // identifiers may be shared among functions
    // (e.g., due to inlining or other code restructuring)
    
    irep_idt l1_name;
    unsigned offset=0;
    
    do
    {
      frame.level1.rename(l0_name, frame_nr+offset);
      l1_name=frame.level1(l0_name);
      offset++;
    }
    while(state.l1_history.find(l1_name)!=state.l1_history.end());
    
    // now unique -- store
    frame.local_variables.insert(l1_name);
    state.l1_history.insert(l1_name);
  }
}

/*******************************************************************\

Function: goto_symext::return_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::return_assignment(statet &state)
{
  statet::framet &frame=state.top();

  const goto_programt::instructiont &instruction=*state.source.pc;
  assert(instruction.is_return());
  const code_returnt &code=to_code_return(instruction.code);

  target.location(state.guard, state.source);

  if(code.operands().size()==1)
  {
    exprt value=code.op0();

    clean_expr(value, state, false);
  
    if(frame.return_value.is_not_nil())
    {
      code_assignt assignment(frame.return_value, value);

      assert(
        ns.follow(assignment.lhs().type())==
        ns.follow(assignment.rhs().type()));
      basic_symext::symex_assign(state, assignment);
    }
  }
  else
  {
    if(frame.return_value.is_not_nil())
      throw "return with unexpected value";
  }
}

/*******************************************************************\

Function: goto_symext::symex_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_return(statet &state)
{
  return_assignment(state);

  // we treat this like an unconditional
  // goto to the end of the function

  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[state.top().end_of_function];

  goto_state_list.push_back(statet::goto_statet(state));

  // kill this one
  state.guard.make_false();
}

/*******************************************************************\

Function: goto_symext::symex_step_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_step_return(statet &state)
{
  return_assignment(state);
}

