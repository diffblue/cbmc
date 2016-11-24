/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/byte_operators.h>
#include <util/i2string.h>
#include <util/pointer_offset_size.h>
#include <util/expr_util.h>
#include <util/base_type.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>

#include "path_symex_class.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: path_symext::propagate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symext::propagate(const exprt &src)
{
  // propagate things that are 'simple enough'
  if(src.is_constant())
    return true;
  else if(src.id()==ID_member)
    return propagate(to_member_expr(src).struct_op());
  else if(src.id()==ID_index)
    return false;
  else if(src.id()==ID_typecast)
    return propagate(to_typecast_expr(src).op());
  else if(src.id()==ID_symbol)
    return true;
  else if(src.id()==ID_address_of)
    return true;
  else if(src.id()==ID_plus)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_array)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_vector)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(src);
    if(!propagate(if_expr.true_case())) return false;
    if(!propagate(if_expr.false_case())) return false;
    return true;
  }
  else if(src.id()==ID_array_of)
  {
    return propagate(to_array_of_expr(src).what());
  }
  else if(src.id()==ID_union)
  {
    return propagate(to_union_expr(src).op());
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: path_symext::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::assign(
  path_symex_statet &state,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.id()==ID_side_effect) // catch side effects on rhs
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      symex_malloc(state, lhs, side_effect_expr);
      return;
    }
    else if(statement==ID_nondet)
    {
      // done in statet:instantiate_rec
    }
    else
      throw "unexpected side-effect on rhs: "+id2string(statement);
  }

  // read the address of the lhs, with propagation
  exprt lhs_address=state.read(address_of_exprt(lhs));
  
  // now SSA the lhs, no propagation
  exprt ssa_lhs=
    state.read_no_propagate(dereference_exprt(lhs_address));

  // read the rhs
  exprt ssa_rhs=state.read(rhs);

  // start recursion on lhs
  exprt::operandst _guard; // start with empty guard
  assign_rec(state, _guard, ssa_lhs, ssa_rhs);
}

/*******************************************************************\

Function: path_symext::symex_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil()) return t;
    }
  }
  
  return nil_typet();
}

void path_symext::symex_malloc(
  path_symex_statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";
    
  // increment dynamic object counter
  unsigned dynamic_count=++state.var_map.dynamic_count;
  
  exprt size=code.op0();
  typet object_type=nil_typet();
  
  {
    exprt tmp_size=state.read(size); // to allow constant propagation
    
    // special treatment for sizeof(T)*x
    if(tmp_size.id()==ID_mult &&
       tmp_size.operands().size()==2 &&
       tmp_size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(tmp_size.op0()),
        tmp_size.op1());      
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);
      
      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(tmp_type, state.var_map.ns);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(tmp_size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;
            
            if(elements*elem_size==alloc_size)
              object_type=array_typet(tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }
    
    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed
    
    if(object_type.id()==ID_array &&
       !to_array_type(object_type).size().is_constant())
    {
      exprt &size=to_array_type(object_type).size();
    
      symbolt size_symbol;

      size_symbol.base_name="dynamic_object_size"+i2string(dynamic_count);
      size_symbol.name="symex::"+id2string(size_symbol.base_name);
      size_symbol.is_lvalue=true;
      size_symbol.type=tmp_size.type();
      size_symbol.mode=ID_C;

      //state.var_map(size_symbol.name, suffix, size_symbol.type);

      assign(state,
             size_symbol.symbol_expr(), 
             size);

      size=size_symbol.symbol_expr();
    }
  }
  
  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+i2string(state.var_map.dynamic_count);
  value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=ID_C;

  //state.var_map(value_symbol.name, suffix, value_symbol.type);

  address_of_exprt rhs;
  
  if(object_type.id()==ID_array)
  {
    rhs.type()=pointer_typet(value_symbol.type.subtype());
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=gen_zero(index_type());
    rhs.op0()=index_expr;
  }
  else
  {
    rhs.op0()=value_symbol.symbol_expr();
    rhs.type()=pointer_typet(value_symbol.type);
  }
  
  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  assign(state, lhs, rhs);
}

/*******************************************************************\

Function: path_symext::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::assign_rec(
  path_symex_statet &state,
  exprt::operandst &guard, 
  const exprt &ssa_lhs, 
  const exprt &ssa_rhs)
{
  //const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs.type());
  
  #ifdef DEBUG
  std::cout << "assign_rec: " << ssa_lhs.pretty() << std::endl;
  //std::cout << "ssa_lhs_type: " << ssa_lhs_type.id() << std::endl;
  #endif
  
  if(ssa_lhs.id()==ID_symbol)
  {
    // These are expected to be SSA symbols
    assert(ssa_lhs.get_bool(ID_C_SSA_symbol));
    
    const symbol_exprt &symbol_expr=to_symbol_expr(ssa_lhs);
    const irep_idt &full_identifier=symbol_expr.get(ID_C_full_identifier);
    
    #ifdef DEBUG
    const irep_idt &ssa_identifier=symbol_expr.get_identifier();
    std::cout << "SSA symbol identifier: " << ssa_identifier << std::endl;
    std::cout << "full identifier: " << full_identifier << std::endl;
    #endif
    
    var_mapt::var_infot &var_info=state.var_map[full_identifier];
    assert(var_info.full_identifier==full_identifier);

    // increase the SSA counter and produce new SSA symbol expression
    var_info.increment_ssa_counter();
    symbol_exprt new_lhs=var_info.ssa_symbol();

    #ifdef DEBUG
    std::cout << "new_lhs: " << new_lhs.get_identifier() << std::endl;
    #endif

    // record new state of lhs
    {
      // reference is not stable
      path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
      var_state.ssa_symbol=new_lhs;
    }

    // rhs nil means non-det assignment
    if(ssa_rhs.is_nil())
    {
      path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
      var_state.value=nil_exprt();
    }
    else
    {
      // consistency check
      if(!base_type_eq(ssa_rhs.type(), new_lhs.type(), state.var_map.ns))
      {
        #ifdef DEBUG
        std::cout << "ssa_rhs: " << ssa_rhs.pretty() << std::endl;
        std::cout << "new_lhs: " << new_lhs.pretty() << std::endl;
        #endif
        throw "assign_rec got different types";
      }

      // record the step
      state.record_step();
      stept &step=*state.history;
      
      if(!guard.empty()) step.guard=conjunction(guard);
      step.full_lhs=ssa_lhs;
      step.ssa_lhs=new_lhs;
      step.ssa_rhs=ssa_rhs;

      // propagate the rhs?
      path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
      var_state.value=propagate(ssa_rhs)?ssa_rhs:nil_exprt();
    }
  }
  else if(ssa_lhs.id()==ID_member)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_member" << std::endl;
    #endif

    const member_exprt &ssa_lhs_member_expr=to_member_expr(ssa_lhs);
    const exprt &struct_op=ssa_lhs_member_expr.struct_op();

    const typet &compound_type=
      state.var_map.ns.follow(struct_op.type());
  
    if(compound_type.id()==ID_struct)
    {
      // We flatten the top-level structs, so this one is inside an
      // array or a union.

      exprt member_name(ID_member_name);
      member_name.set(ID_component_name, ssa_lhs_member_expr.get_component_name());
            
      with_exprt new_rhs(struct_op, member_name, ssa_rhs);
      
      assign_rec(state, guard, struct_op, new_rhs);
    }
    else if(compound_type.id()==ID_union)
    {
      // rewrite into byte_extract, and do again
      exprt offset=gen_zero(index_type());

      byte_extract_exprt new_lhs(byte_update_id(), struct_op, offset, ssa_rhs.type());
      
      assign_rec(state, guard, new_lhs, ssa_rhs);
    }
    else
      throw "assign_rec: member expects struct or union type";
  }
  else if(ssa_lhs.id()==ID_index)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_index" << std::endl;
    #endif

    throw "unexpected array index on lhs";    
  }
  else if(ssa_lhs.id()==ID_dereference)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_dereference" << std::endl;
    #endif

    throw "unexpected dereference on lhs";
  }
  else if(ssa_lhs.id()==ID_if)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_if" << std::endl;
    #endif

    const if_exprt &lhs_if_expr=to_if_expr(ssa_lhs);
    exprt cond=lhs_if_expr.cond();

    // true
    guard.push_back(cond);
    assign_rec(state, guard, lhs_if_expr.true_case(), ssa_rhs);
    guard.pop_back();
    
    // false
    guard.push_back(not_exprt(cond));
    assign_rec(state, guard, lhs_if_expr.false_case(), ssa_rhs);
    guard.pop_back();
  }
  else if(ssa_lhs.id()==ID_byte_extract_little_endian ||
          ssa_lhs.id()==ID_byte_extract_big_endian)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_byte_extract" << std::endl;
    #endif

    const byte_extract_exprt &byte_extract_expr=
      to_byte_extract_expr(ssa_lhs);
  
    // assignment to byte_extract operators:
    // turn into byte_update operator
    
    irep_idt new_id;
    
    if(ssa_lhs.id()==ID_byte_extract_little_endian)
      new_id=ID_byte_update_little_endian;
    else if(ssa_lhs.id()==ID_byte_extract_big_endian)
      new_id=ID_byte_update_big_endian;
    else
      assert(false);

    byte_update_exprt new_rhs(new_id);

    new_rhs.type()=byte_extract_expr.op().type();
    new_rhs.op()=byte_extract_expr.op();
    new_rhs.offset()=byte_extract_expr.offset();
    new_rhs.value()=ssa_rhs;
    
    const exprt new_lhs=byte_extract_expr.op();

    assign_rec(state, guard, new_lhs, new_rhs);
  }
  else if(ssa_lhs.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(state.var_map.ns.follow(ssa_lhs.type()));
    const struct_typet::componentst &components=
      struct_type.components();
    
    // split up into components
    const exprt::operandst &operands=ssa_lhs.operands();
    
    assert(operands.size()==components.size());
    
    for(unsigned i=0; i<components.size(); i++)
    {
      exprt new_rhs=
        ssa_rhs.is_nil()?ssa_rhs:
        simplify_expr(member_exprt(ssa_rhs, components[i].get_name(), components[i].type()),
          state.var_map.ns);
      assign_rec(state, guard, operands[i], new_rhs);
    }
  }
  else if(ssa_lhs.id()==ID_array)
  {
    const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs.type());
  
    if(ssa_lhs_type.id()!=ID_array)
      throw "array constructor must have array type";
      
    const array_typet &array_type=
      to_array_type(ssa_lhs_type);
      
    const exprt::operandst &operands=ssa_lhs.operands();
    
    // split up into elements
    for(unsigned i=0; i<operands.size(); i++)
    {
      exprt new_rhs=
        ssa_rhs.is_nil()?ssa_rhs:
        simplify_expr(index_exprt(ssa_rhs, from_integer(i, index_type()), array_type.subtype()),
          state.var_map.ns);
      assign_rec(state, guard, operands[i], new_rhs);
    }
  }
  else if(ssa_lhs.id()==ID_vector)
  {
    const vector_typet &vector_type=
      to_vector_type(state.var_map.ns.follow(ssa_lhs.type()));
    
    const exprt::operandst &operands=ssa_lhs.operands();
    
    // split up into elements
    for(unsigned i=0; i<operands.size(); i++)
    {
      exprt new_rhs=
        ssa_rhs.is_nil()?ssa_rhs:
        simplify_expr(index_exprt(ssa_rhs, from_integer(i, index_type()), vector_type.subtype()),
          state.var_map.ns);
      assign_rec(state, guard, operands[i], new_rhs);
    }
  }
  else if(ssa_lhs.id()==ID_string_constant ||
          ssa_lhs.id()=="NULL-object" ||
          ssa_lhs.id()=="zero_string" ||
          ssa_lhs.id()=="is_zero_string" ||
          ssa_lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else
  {
    // ignore
    throw "path_symext::assign_rec(): unexpected lhs: "+ssa_lhs.id_string();
  }
}

/*******************************************************************\

Function: path_symext::function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::function_call_rec(
  path_symex_statet &state,
  const code_function_callt &call,
  const exprt &function,
  std::list<path_symex_statet> &further_states)
{
  #ifdef DEBUG
  std::cout << "function_call_rec: " << function.pretty() << std::endl;
  #endif

  if(function.id()==ID_symbol)
  {
    const irep_idt &function_identifier=
      to_symbol_expr(function).get_identifier();

    // find the function
    locst::function_mapt::const_iterator f_it=
      state.locs.function_map.find(function_identifier);

    if(f_it==state.locs.function_map.end())
      throw "failed to find `"+id2string(function_identifier)+"' in function_map";
  
    const locst::function_entryt &function_entry=f_it->second;

    loc_reft function_entry_point=function_entry.first_loc;
  
    // do we have a body?
    if(function_entry_point==loc_reft())
    {
      // no body, this is a skip
      if(call.lhs().is_not_nil())
        assign(state, call.lhs(), nil_exprt());

      state.next_pc();
      return;
    }
  
    // push a frame on the call stack
    path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];
    thread.call_stack.push_back(path_symex_statet::framet());
    thread.call_stack.back().current_function=function_identifier;
    thread.call_stack.back().return_location=thread.pc.next_loc();
    thread.call_stack.back().return_lhs=call.lhs();

    #if 0
    for(loc_reft l=function_entry_point; ; ++l)
    {
      if(locs[l].target->is_end_function()) break;
      if(locs[l].target->is_decl())
      {
        // make sure we have the local in the var_map
        state.
      }
    }
    
    // save the locals into the frame
    for(locst::local_variablest::const_iterator
        it=function_entry.local_variables.begin();
        it!=function_entry.local_variables.end();
        it++)
    {
      unsigned nr=state.var_map[*it].number;
      thread.call_stack.back().saved_local_vars[nr]=thread.local_vars[nr];
    }    
    #endif

    const code_typet &code_type=function_entry.type;

    const code_typet::parameterst &function_parameters=code_type.parameters();

    const exprt::operandst &call_arguments=call.arguments();
  
    // now assign the argument values to parameters
    for(unsigned i=0; i<call_arguments.size(); i++)
    {
      if(i<function_parameters.size())
      {
        const code_typet::parametert &function_parameter=function_parameters[i];
        irep_idt identifier=function_parameter.get_identifier();

        if(identifier==irep_idt())
          throw "function_call " + id2string(function_identifier) + " no identifier for function parameter";

        symbol_exprt lhs(identifier, function_parameter.type());
            
        assign(state, lhs, call_arguments[i]);
      }
    }

    // update statistics
    state.recursion_map[function_identifier]++;

    // set the new PC
    thread.pc=function_entry_point;
  }
  else if(function.id()==ID_dereference)
  {
    // should not happen, we read() before
    throw "function_call_rec got dereference";
  }
  else if(function.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(function);
    exprt guard=if_expr.cond();
    
    // add a 'further state' for the false-case
    
    {
      further_states.push_back(state);
      path_symex_statet &false_state=further_states.back();
      false_state.record_step();
      false_state.history->guard=not_exprt(guard);
      function_call_rec(further_states.back(), call, if_expr.false_case(), further_states);
    }

    // do the true-case in 'state'
    {
      state.record_step();
      state.history->guard=guard;
      function_call_rec(state, call, if_expr.true_case(), further_states);
    }
  }
  else
    throw "TODO: function_call "+function.id_string();
}

/*******************************************************************\

Function: path_symext::return_from_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::return_from_function(
  path_symex_statet &state,
  const exprt &return_value)
{
  path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];

  // returning from very last function?
  if(thread.call_stack.empty())
  {
    state.disable_current_thread();
  }
  else
  {
    // update statistics
    state.recursion_map[thread.call_stack.back().current_function]--;
  
    // set PC to return location
    thread.pc=thread.call_stack.back().return_location;

    // assign the return value
    if(return_value.is_not_nil() &&
       thread.call_stack.back().return_lhs.is_not_nil())
      assign(state, thread.call_stack.back().return_lhs, return_value);

    // restore the local variables
    for(path_symex_statet::var_state_mapt::const_iterator
        it=thread.call_stack.back().saved_local_vars.begin();
        it!=thread.call_stack.back().saved_local_vars.end();
        it++)
      thread.local_vars[it->first]=it->second;

    // kill the frame
    thread.call_stack.pop_back();
  }
}

/*******************************************************************\

Function: path_symext::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::do_goto(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  const loct &loc=state.locs[state.pc()];
  assert(!loc.branch_target.is_nil());

  exprt guard=state.read(instruction.guard);
  
  if(guard.is_true()) // branch taken always
  {
    state.record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    state.set_pc(loc.branch_target);
    return; // we are done
  }

  if(!guard.is_false())
  {
    // branch taken case
    // copy the state into 'furhter_states'
    further_states.push_back(state);
    further_states.back().record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    further_states.back().set_pc(loc.branch_target);
    further_states.back().history->guard=guard;
  }

  // branch not taken case
  exprt negated_guard=not_exprt(guard);
  state.record_step();
  state.history->branch=stept::BRANCH_NOT_TAKEN;
  state.next_pc();
  state.history->guard=negated_guard;
}

/*******************************************************************\

Function: path_symext::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::do_goto(
  path_symex_statet &state,
  bool taken)
{
  state.record_step();

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  exprt guard=state.read(instruction.guard);
  
  if(taken)
  {
    // branch taken case
    const loct &loc=state.locs[state.pc()];
    assert(!loc.branch_target.is_nil());
    state.set_pc(loc.branch_target);
    state.history->guard=guard;
    state.history->branch=stept::BRANCH_TAKEN;
  }
  else
  {
    // branch not taken case
    exprt negated_guard=not_exprt(guard);
    state.next_pc();
    state.history->guard=negated_guard;
    state.history->branch=stept::BRANCH_NOT_TAKEN;
  }
}

/*******************************************************************\

Function: path_symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::operator()(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();
    
  #ifdef DEBUG
  std::cout << "path_symext::operator(): "
            << state.pc() << " "
            << instruction.type
            << std::endl;
  #endif

  switch(instruction.type)
  {
  case END_FUNCTION:
    // pop the call stack
    state.record_step();
    return_from_function(state, nil_exprt());
    break;
    
  case RETURN:
    // pop the call stack
    {
      state.record_step();
      exprt return_val=instruction.code.operands().size()==1?
                       instruction.code.op0():nil_exprt();
      return_from_function(state, return_val);
    }
    break;
    
  case START_THREAD:
    {
      const loct &loc=state.locs[state.pc()];
      assert(!loc.branch_target.is_nil());
      
      state.record_step();
      state.next_pc();
      
      // ordering of the following matters due to vector instability
      path_symex_statet::threadt &new_thread=state.add_thread();
      path_symex_statet::threadt &old_thread=state.threads[state.get_current_thread()];
      new_thread.pc=loc.branch_target;
      new_thread.local_vars=old_thread.local_vars;
    }
    break;
    
  case END_THREAD:
    state.record_step();
    state.disable_current_thread();
    break;
    
  case GOTO:
    do_goto(state, further_states);
    break;
    
  case CATCH:
    // ignore for now
    state.record_step();
    state.next_pc();
    break;
    
  case THROW:
    state.record_step();
    throw "THROW not yet implemented";
    
  case ASSUME:
    state.record_step();
    state.next_pc();
    if(instruction.guard.is_false())
      state.disable_current_thread();
    else
    {
      exprt guard=state.read(instruction.guard);
      state.history->guard=guard;
    }
    break;
    
  case ASSERT:
  case SKIP:
  case LOCATION:
  case DEAD:
    state.record_step();
    state.next_pc();
    break;

  case DECL:
    // assigning an RHS of NIL means 'nondet'
    assign(state, to_code_decl(instruction.code).symbol(), nil_exprt());
    state.next_pc();
    break;

  case ATOMIC_BEGIN:
    if(state.inside_atomic_section)
      throw "nested ATOMIC_BEGIN";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=true;
    break;

  case ATOMIC_END:
    if(!state.inside_atomic_section)
      throw "ATOMIC_END unmatched";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=false;
    break;
    
  case ASSIGN:
    assign(state, to_code_assign(instruction.code));
    state.next_pc();
    break;
    
  case FUNCTION_CALL:
    state.record_step();
    function_call(state, to_code_function_call(instruction.code), further_states);
    break;
    
  case OTHER:
    state.record_step();

    {
      const codet &code=instruction.code;
      const irep_idt &statement=code.get_statement();

      if(statement==ID_expression)
      {
        // like SKIP
      }
      else if(statement==ID_printf)
      {
        // ignore for now (should record stuff printed)
      }
      else if(statement==ID_asm)
      {
        // ignore for now
      }
      else if(statement==ID_fence)
      {
        // ignore for SC
      }
      else
        throw "unexpected OTHER statement: "+id2string(statement);
    }

    state.next_pc();
    break;

  default:
    throw "path_symext: unexpected instruction";
  }
}

/*******************************************************************\

Function: path_symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::operator()(path_symex_statet &state)
{
  std::list<path_symex_statet> further_states;
  operator()(state, further_states);
  if(!further_states.empty())
    throw "path_symext got unexpected further states";
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  path_symext path_symex;
  path_symex(state, further_states);
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex(path_symex_statet &state)
{
  path_symext path_symex;
  path_symex(state);
}

/*******************************************************************\

Function: path_symex_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_goto(
  path_symex_statet &state,
  bool taken)
{
  path_symext path_symex;
  path_symex.do_goto(state, taken);
}

/*******************************************************************\

Function: path_symex_assert_fail

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_assert_fail(path_symex_statet &state)
{
  path_symext path_symex;
  path_symex.do_assert_fail(state);
}

