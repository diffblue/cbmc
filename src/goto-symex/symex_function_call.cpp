/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <sstream>
#include <cassert>

#include <util/expr_util.h>
#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

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
  const unsigned thread_nr,
  unsigned unwind)
{
  return false;
}

/*******************************************************************\

Function: goto_symext::parameter_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::parameter_assignments(
  const irep_idt function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  statet &state,
  const exprt::operandst &arguments)
{
  const code_typet &function_type=goto_function.type;

  // iterates over the arguments
  exprt::operandst::const_iterator it1=arguments.begin();

  // these are the types of the parameters
  const code_typet::parameterst &parameter_types=
    function_type.parameters();

  // iterates over the types of the parameters
  for(code_typet::parameterst::const_iterator
      it2=parameter_types.begin();
      it2!=parameter_types.end();
      it2++)
  {
    const code_typet::parametert &parameter=*it2;

    // this is the type that the n-th argument should have
    const typet &parameter_type=parameter.type();

    const irep_idt &identifier=parameter.get_identifier();

    if(identifier==irep_idt())
      throw "no identifier for function parameter";

    const symbolt &symbol=ns.lookup(identifier);
    symbol_exprt lhs=symbol.symbol_expr();

    exprt rhs;

    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      std::string warn=
        "call to `"+id2string(function_identifier)+"': "
        "not enough arguments, inserting non-deterministic value\n";
      std::cerr << state.source.pc->source_location.as_string()+": "+warn;

      rhs=side_effect_expr_nondett(parameter_type);
    }
    else
      rhs=*it1;

    if(rhs.is_nil())
    {
      // 'nil' argument doesn't get assigned
    }
    else
    {
      // It should be the same exact type.
      if(!base_type_eq(parameter_type, rhs.type(), ns))
      {
        const typet &f_parameter_type=ns.follow(parameter_type);
        const typet &f_rhs_type=ns.follow(rhs.type());

        // But we are willing to do some limited conversion.
        // This is highly dubious, obviously.
        if((f_parameter_type.id()==ID_signedbv ||
            f_parameter_type.id()==ID_unsignedbv ||
            f_parameter_type.id()==ID_c_enum_tag ||
            f_parameter_type.id()==ID_bool ||
            f_parameter_type.id()==ID_pointer ||
            f_parameter_type.id()==ID_union) &&
           (f_rhs_type.id()==ID_signedbv ||
            f_rhs_type.id()==ID_unsignedbv ||
            f_rhs_type.id()==ID_c_bit_field ||
            f_rhs_type.id()==ID_c_enum_tag ||
            f_rhs_type.id()==ID_bool ||
            f_rhs_type.id()==ID_pointer ||
            f_rhs_type.id()==ID_union))
        {
          rhs=
            byte_extract_exprt(
              byte_extract_id(),
              rhs,
              gen_zero(index_type()),
              parameter_type);
        }
        else
        {
          std::ostringstream error;
          error << "function call: parameter \"" << identifier
                << "\" type mismatch: got " << rhs.type().pretty()
                << ", expected " << parameter_type.pretty();
          throw error.str();
        }
      }

      symex_assign_rec(state, code_assignt(lhs, rhs));
    }

    if(it1!=arguments.end())
      it1++;
  }

  if(function_type.has_ellipsis())
  {
    // These are va_arg arguments; their types may differ from call to call
    unsigned va_count=0;
    const symbolt *va_sym=0;
    while(!ns.lookup(id2string(function_identifier)+"::va_arg"+i2string(va_count),
                    va_sym))
      ++va_count;

    for( ; it1!=arguments.end(); it1++, va_count++)
    {
      irep_idt id=id2string(function_identifier)+"::va_arg"+i2string(va_count);

      // add to symbol table
      symbolt symbol;
      symbol.name=id;
      symbol.base_name="va_arg"+i2string(va_count);
      symbol.type=it1->type();

      new_symbol_table.move(symbol);

      symbol_exprt lhs=symbol_exprt(id, it1->type());

      symex_assign_rec(state, code_assignt(lhs, *it1));
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
  target.location(state.guard.as_expr(), state.source);

  assert(code.function().id()==ID_symbol);

  const irep_idt &identifier=
    to_symbol_expr(code.function()).get_identifier();

  if(identifier=="CBMC_trace")
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

  const bool stop_recursing=get_unwind_recursion(
    identifier,
    state.source.thread_nr,
    state.top().loop_iterations[identifier].count);

  // see if it's too much
  if(stop_recursing)
  {
    if(options.get_bool_option("partial-loops"))
    {
      // it's ok, ignore
    }
    else
    {
      if(options.get_bool_option("unwinding-assertions"))
        vcc(false_exprt(), "recursion unwinding assertion", state);

      // add to state guard to prevent further assignments
      state.guard.add(false_exprt());
    }

    state.source.pc++;
    return;
  }

  // record the call
  target.function_call(state.guard.as_expr(), identifier, state.source);

  if(!goto_function.body_available())
  {
    no_body(identifier);

    // record the return
    target.function_return(state.guard.as_expr(), identifier, state.source);

    if(call.lhs().is_not_nil())
    {
      side_effect_expr_nondett rhs(call.lhs().type());
      rhs.add_source_location()=call.source_location();
      code_assignt code(call.lhs(), rhs);
      symex_assign_rec(state, code);
    }

    state.source.pc++;
    return;
  }

  // read the arguments -- before the locality renaming
  exprt::operandst arguments=call.arguments();
  for(unsigned i=0; i<arguments.size(); i++)
    state.rename(arguments[i], ns);

  // produce a new frame
  assert(!state.call_stack().empty());
  goto_symex_statet::framet &frame=state.new_frame();

  // preserve locality of local variables
  locality(identifier, state, goto_function);

  // assign actuals to formal parameters
  parameter_assignments(identifier, goto_function, state, arguments);

  frame.end_of_function=--goto_function.body.instructions.end();
  frame.return_value=call.lhs();
  frame.calling_location=state.source;
  frame.function_identifier=identifier;
  frame.hidden_function=goto_function.is_hidden();

  const goto_symex_statet::framet &p_frame=state.previous_frame();
  for(goto_symex_statet::framet::loop_iterationst::const_iterator
      it=p_frame.loop_iterations.begin();
      it!=p_frame.loop_iterations.end();
      ++it)
    if(it->second.is_recursion)
      frame.loop_iterations.insert(*it);

  // increase unwinding counter
  frame.loop_iterations[identifier].is_recursion=true;
  frame.loop_iterations[identifier].count++;

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
  assert(!state.call_stack().empty());

  {
    statet::framet &frame=state.top();

    // restore program counter
    state.source.pc=frame.calling_location.pc;

    // restore L1 renaming
    state.level1.restore_from(frame.old_level1);

    // clear function-locals from L2 renaming
    for(goto_symex_statet::renaming_levelt::current_namest::iterator
        c_it=state.level2.current_names.begin();
        c_it!=state.level2.current_names.end();
       ) // no ++c_it
    {
      const irep_idt l1_o_id=c_it->second.first.get_l1_object_identifier();
      // could use iteration over local_objects as l1_o_id is prefix
      if(frame.local_objects.find(l1_o_id)==frame.local_objects.end())
      {
        ++c_it;
        continue;
      }
      goto_symex_statet::renaming_levelt::current_namest::iterator
        cur=c_it;
      ++c_it;
      state.level2.current_names.erase(cur);
    }
  }

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
  target.function_return(
    state.guard.as_expr(), state.source.pc->function, state.source);

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
  const irep_idt function_identifier,
  statet &state,
  const goto_functionst::goto_functiont &goto_function)
{
  unsigned &frame_nr=
    state.threads[state.source.thread_nr].function_frame[function_identifier];
  frame_nr++;

  std::set<irep_idt> local_identifiers;

  get_local_identifiers(goto_function, local_identifiers);

  statet::framet &frame=state.top();

  for(std::set<irep_idt>::const_iterator
      it=local_identifiers.begin();
      it!=local_identifiers.end();
      it++)
  {
    // get L0 name
    ssa_exprt ssa(ns.lookup(*it).symbol_expr());
    state.rename(ssa, ns, goto_symex_statet::L0);
    const irep_idt l0_name=ssa.get_identifier();

    // save old L1 name for popping the frame
    statet::level1t::current_namest::const_iterator c_it=
      state.level1.current_names.find(l0_name);

    if(c_it!=state.level1.current_names.end())
      frame.old_level1[l0_name]=c_it->second;

    // do L1 renaming -- these need not be unique, as
    // identifiers may be shared among functions
    // (e.g., due to inlining or other code restructuring)

    state.level1.current_names[l0_name]=
      std::make_pair(ssa, frame_nr);
    state.rename(ssa, ns, goto_symex_statet::L1);

    irep_idt l1_name=ssa.get_identifier();
    unsigned offset=0;

    while(state.l1_history.find(l1_name)!=state.l1_history.end())
    {
      state.level1.increase_counter(l0_name);
      ++offset;
      ssa.set_level_1(frame_nr+offset);
      l1_name=ssa.get_identifier();
    }

    // now unique -- store
    frame.local_objects.insert(l1_name);
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

  target.location(state.guard.as_expr(), state.source);

  if(code.operands().size()==1)
  {
    exprt value=code.op0();

    if(frame.return_value.is_not_nil())
    {
      code_assignt assignment(frame.return_value, value);

      if(!base_type_eq(assignment.lhs().type(),
                       assignment.rhs().type(), ns))
        throw "goto_symext::return_assignment type mismatch at "+
              instruction.source_location.as_string()+":\n"+
              "assignment.lhs().type():\n"+assignment.lhs().type().pretty()+"\n"+
              "assignment.rhs().type():\n"+assignment.rhs().type().pretty();

      symex_assign_rec(state, assignment);
    }
  }
  else
  {
    if(frame.return_value.is_not_nil())
      throw "return with unexpected value";
  }
}
