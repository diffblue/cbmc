/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <cstdio>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <string.h>

#include <util/std_types.h>
#include <util/symbol_table.h>
#include <util/ieee_float.h>
#include <util/fixedbv.h>
#include <util/std_expr.h>
#include <util/message.h>
#include <util/string2int.h>
#include <ansi-c/c_types.h>
#include <json/json_parser.h>

#include "interpreter.h"
#include "interpreter_class.h"
#include "remove_returns.h"

/*******************************************************************\

Function: interpretert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::operator()()
{
  show=true;
  message->status() << "0- Initialize:" << messaget::eom;
  initialise(true);
  try
  {
    std::cout << "Type h for help" << std::endl;
    while(!done) command();
    message->status() << total_steps << "- Program End." 
                      << messaget::endl << messaget::eom;
  }
  catch (const char *e)
  {
    message->error() << e << messaget::endl << messaget::eom;
  }
  while(!done) command();
}

/*******************************************************************

Function: interpretert::initialise

 Inputs:

 Outputs:

 Purpose: Initialises the memory map of the interpreter and 
          [optionally] runs up to the entry point (thus doing 
          non-program initialization)

 \*******************************************************************/

void interpretert::initialise(bool init) {
  build_memory_map();
  
  total_steps=0;
  const goto_functionst::function_mapt::const_iterator
    main_it=goto_functions.function_map.find(goto_functionst::entry_point());

  if(main_it==goto_functions.function_map.end())
    throw "main not found";
  
  const goto_functionst::goto_functiont &goto_function=main_it->second;
  
  if(!goto_function.body_available())
    throw "main has no body";

  PC=goto_function.body.instructions.begin();
  function=main_it;
    
  done=false;
  if(init) {
    stack_depth=call_stack.size()+1;
    show_state();
    step();
    while(!done && (stack_depth<=call_stack.size()) && (stack_depth>=0)) 
    {
      show_state();
      step();
    }
    while(!done && (call_stack.size()==0))
    {
      show_state();
      step();
    }
    clear_input_flags();
    input_vars.clear();
  }
}

/*******************************************************************\

Function: interpretert::show_state

  Inputs:

 Outputs:

 Purpose: displays the current position of the pc and corresponding
          code

\*******************************************************************/

void interpretert::show_state()
{
  if(!show) return;
  message->status() << messaget::endl;
  message->status() << total_steps+1 << " ----------------------------------------------------"
           << messaget::endl;

  if(PC==function->second.body.instructions.end())
  {
      message->status() << "End of function `"
              << function->first << "'" << messaget::endl;
  }
  else
    function->second.body.output_instruction(ns, function->first, 
                                             message->status(), PC);

  message->status() << messaget::eom;
}

/*******************************************************************\

Function: interpretert::command

  Inputs:

 Outputs:

 Purpose: reads a user command and rus it.

\*******************************************************************/

void interpretert::command()
{
  #define BUFSIZE 100
  char command[BUFSIZE]; 
  if(fgets(command, BUFSIZE-1, stdin)==NULL)
  {
    done=true;
    return;
  }

  char ch=tolower(command[0]);
  if(ch=='q')
    done=true;
  else if(ch=='h')
  {
    std::cout << "Interpreter help" << std::endl;
    std::cout << "h: display this menu" << std::endl;
    std::cout << "i: output program inputs" << std::endl;
    std::cout << "id: output program inputs with det values for don cares" 
              << std::endl;
    std::cout << "in: output program inputs with non-det values for don cares" 
              << std::endl;
    std::cout << "it: output program inputs for last trace" << std::endl;
    std::cout << "if: output program inputs ids for non-bodied function"
              << std::endl;
    std::cout << "i file: output program inputs for [json] file trace"
              << std::endl;
    std::cout << "j: output json trace" << std::endl;
    std::cout << "m: output memory dump" << std::endl;
    std::cout << "o: output goto trace" << std::endl;
    std::cout << "q: quit" << std::endl;
    std::cout << "r: run until completion" << std::endl;
    std::cout << "s#: step a number of instructions" << std::endl;
    std::cout << "sa: step across a function" << std::endl;
    std::cout << "so: step out of a function" << std::endl;
  }
  else if(ch=='i')
  {
    ch=tolower(command[1]);
    if(ch=='d')      list_inputs(false);
    else if(ch=='n') list_inputs(true);
    else if(ch=='t') {
      list_input_varst ignored;
      side_effects_differencet diffs;
      load_counter_example_inputs(steps, ignored, diffs);
    }
    else if(ch==' ') load_counter_example_inputs(command+3);
    else if(ch=='f') {
      list_non_bodied();
      show_state();
      return;
    }
    print_inputs();
  }
  else if(ch=='j')
  {
    jsont json_steps;
    convert(ns, steps, json_steps);
    ch=tolower(command[1]);
    if(ch==' ') {
      std::ofstream file;
      file.open(command+2);
      if(file.is_open())
      {
        json_steps.output(file);
        file.close();
        return;
      }
    }
    json_steps.output(message->result());
  }
  else if(ch=='m')
  {
    ch=tolower(command[1]);
    print_memory(ch=='i');
  }
  else if(ch=='o')
  {
    ch=tolower(command[1]);
    if(ch==' ')
    {
      std::ofstream file;
      file.open(command+2);
      if(file.is_open())
      {
        steps.output(ns, file);
        file.close();
        return;
      }
    }
    steps.output(ns, message->result());
  }
  else if(ch=='r')
  {
    ch=tolower(command[1]);
    initialise(ch!='0');
  }
  else if((ch=='s') || (ch==0))
  {
    num_steps=1;
    stack_depth=-1;
    ch=tolower(command[1]);
    if(ch=='e')
      num_steps=-1;
    else if(ch=='o')
      stack_depth=call_stack.size();
    else if(ch=='a')
      stack_depth=call_stack.size()+1;
    else {
      num_steps=atoi(command+1);
      if(num_steps==0) num_steps=1;
    }
    while(!done && ((num_steps<0) || ((num_steps--)>0)))
    {
      step();
      show_state();
    }
    while(!done && (stack_depth<=call_stack.size())
       && (stack_depth>=0))
    {
      step();
      show_state();
    }
    return;
  }
  show_state();
}

/*******************************************************************\

Function: interpretert::step

  Inputs:

 Outputs:

 Purpose: performs a single step executiona and updates the pc

\*******************************************************************/

void interpretert::step()
{
  total_steps++;
  if(PC==function->second.body.instructions.end())
  {
    if(call_stack.empty())
      done=true;
    else
    {
      PC=call_stack.top().return_PC;
      function=call_stack.top().return_function;
      //stack_pointer=call_stack.top().old_stack_pointer;
      //TODO: this increases memory size quite quickly. Should check alternatives
      call_stack.pop();
    }

    return;
  }
  
  next_PC=PC;
  next_PC++; 

  steps.add_step(goto_trace_stept());
  goto_trace_stept &trace_step=steps.get_last_step();
  trace_step.thread_nr=thread_id;
  trace_step.pc=PC;
  switch(PC->type)
  {
  case GOTO:
    trace_step.type=goto_trace_stept::GOTO;
    execute_goto();
    break;
  
  case ASSUME:
    trace_step.type=goto_trace_stept::ASSUME;
    execute_assume();
    break;
  
  case ASSERT:
    trace_step.type=goto_trace_stept::ASSERT;
    execute_assert();
    break;
  
  case OTHER:
    execute_other();
    break;
  
  case DECL:
    trace_step.type=goto_trace_stept::DECL;
    execute_decl();
    break;
  
  case SKIP:
  case LOCATION:
    trace_step.type=goto_trace_stept::LOCATION;
    break;
  case END_FUNCTION:
    trace_step.type=goto_trace_stept::FUNCTION_RETURN;
    break;
  
  case RETURN:
    trace_step.type=goto_trace_stept::FUNCTION_RETURN;
    if(call_stack.empty())
      throw "RETURN without call";

    if(PC->code.operands().size()==1 &&
       call_stack.top().return_value_address!=0)
    {
      std::vector<mp_integer> rhs;
      evaluate(PC->code.op0(), rhs);
      assign(call_stack.top().return_value_address, rhs);
    }

    next_PC=function->second.body.instructions.end();
    break;
    
  case ASSIGN:
    trace_step.type=goto_trace_stept::ASSIGNMENT;
    execute_assign();
    break;
    
  case FUNCTION_CALL:
    trace_step.type=goto_trace_stept::FUNCTION_CALL;
    execute_function_call();
    break;
  
  case START_THREAD:
    trace_step.type=goto_trace_stept::SPAWN;
    throw "START_THREAD not yet implemented";
  
  case END_THREAD:
    throw "END_THREAD not yet implemented";
    break;

  case ATOMIC_BEGIN:
    trace_step.type=goto_trace_stept::ATOMIC_BEGIN;
    throw "ATOMIC_BEGIN not yet implemented";
    
  case ATOMIC_END:
    trace_step.type=goto_trace_stept::ATOMIC_END;
    throw "ATOMIC_END not yet implemented";
    
  case DEAD:
    trace_step.type=goto_trace_stept::DEAD;
    break;//throw "DEAD not yet implemented";
  case THROW:
    trace_step.type=goto_trace_stept::GOTO;
    while(!done && (PC->type!=CATCH))
    {
      if(PC==function->second.body.instructions.end())
      {
        if(call_stack.empty())
          done=true;
        else
        {
          PC=call_stack.top().return_PC;
          function=call_stack.top().return_function;
          call_stack.pop();
        }
      }
      else
      {
        next_PC=PC;
        next_PC++;
      }
    }
    break;
  case CATCH:
    break;
  default:
    throw "encountered instruction with undefined instruction type";
  }
  PC=next_PC;
}

/*******************************************************************\

Function: interpretert::execute_goto

  Inputs:

 Outputs:

 Purpose: executes a goto instruction

\*******************************************************************/

void interpretert::execute_goto()
{
  if(evaluate_boolean(PC->guard))
  {
    if(PC->targets.empty())
      throw "taken goto without target";
    
    if(PC->targets.size()>=2)
      throw "non-deterministic goto encountered";

    next_PC=PC->targets.front();
  }
}

/*******************************************************************\

Function: interpretert::execute_other

  Inputs:

 Outputs:

 Purpose: executes side effects of 'other' instructions

\*******************************************************************/

void interpretert::execute_other()
{
  const irep_idt &statement=PC->code.get_statement();
  if(statement==ID_expression)
  {
    assert(PC->code.operands().size()==1);
    std::vector<mp_integer> rhs;
    evaluate(PC->code.op0(), rhs);
  }
  else if(statement==ID_array_set)
  {
    std::vector<mp_integer> tmp,rhs;
    evaluate(PC->code.op1(), tmp);
    mp_integer address=evaluate_address(PC->code.op0());
    unsigned size=get_size(PC->code.op0().type());
    while(rhs.size()<size) rhs.insert(rhs.end(),tmp.begin(),tmp.end());
    if(size!=rhs.size())
      message->error() << "!! failed to obtain rhs (" << rhs.size() << " vs. "
                      << size << ")" << messaget::endl << messaget::eom;
    else
    {
      assign(address, rhs);
    }
  }
  else
    throw "unexpected OTHER statement: "+id2string(statement);
}

/*******************************************************************\

Function: interpretert::execute_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::execute_decl()
{
  assert(PC->code.get_statement()==ID_decl);
}

/*******************************************************************

Function: interpretert::get_component_id

 Inputs: an object and a memory offset

 Outputs:

 Purpose: retrieves the member at offset

 \*******************************************************************/
irep_idt interpretert::get_component_id(const irep_idt &object,unsigned offset)
{
  const symbolt &symbol=ns.lookup(object);
  const typet real_type=ns.follow(symbol.type);
  if(real_type.id()!=ID_struct)
    throw "request for member of non-struct";
  const struct_typet &struct_type=to_struct_type(real_type);
  const struct_typet::componentst &components=struct_type.components();
  for(struct_typet::componentst::const_iterator it=components.begin();
      it!=components.end();++it) {
    if(offset<=0) return it->id();
    unsigned size=get_size(it->type());
    assert(size>=0);
    offset -= size;
  }
  return object;
}

/*******************************************************************

Function: interpretert::get_type

 Inputs:

 Outputs:

 Purpose: returns the type object corresponding to id

 \*******************************************************************/
typet interpretert::get_type(const irep_idt &id) const
{
  dynamic_typest::const_iterator it=dynamic_types.find(id);
  if (it==dynamic_types.end()) return symbol_table.lookup(id).type;
  return it->second;
}

/*******************************************************************

Function: interpretert::get_value

 Inputs:

 Outputs:

 Purpose: retrives the constant value at memory location offset
          as an object of type type 

 \*******************************************************************/
exprt interpretert::get_value(const typet &type,
                              unsigned offset,bool use_non_det)
{
  const typet real_type=ns.follow(type);
  if(real_type.id()==ID_struct) {
    exprt result=struct_exprt(real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();
    result.reserve_operands(components.size());
    for(struct_typet::componentst::const_iterator it=components.begin();
        it!=components.end();++it) {
      unsigned size=get_size(it->type());
      assert(size>=0);
      const exprt operand=get_value(it->type(), offset);
      offset += size;
      result.copy_to_operands(operand);
    }
    return result;
  } else if(real_type.id()==ID_array) {
    exprt result=array_exprt(to_array_type(real_type));
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));
    unsigned subtype_size=get_size(type.subtype());
    mp_integer mp_count;
    to_integer(size_expr, mp_count);
    unsigned count=integer2unsigned(mp_count);
    result.reserve_operands(count);
    for(unsigned i=0;i<count;i++) {
      const exprt operand=get_value(type.subtype(),
          offset+i * subtype_size);
      result.copy_to_operands(operand);
    }
    return result;
  }
  if(use_non_det && (memory[offset].initialised>=0))
    return side_effect_expr_nondett(type);
  std::vector<mp_integer> rhs;
  rhs.push_back(memory[offset].value);
  return get_value(type, rhs);
}

/*******************************************************************
 Function: interpretert::get_value

 Inputs:

 Outputs:

 Purpose: returns the value at offset in the form of type given a 
          memory buffer rhs which is typically a structured type

 \*******************************************************************/
exprt interpretert::get_value(const typet &type,
                              std::vector<mp_integer> &rhs,unsigned offset)
{
  const typet real_type=ns.follow(type);

  if(real_type.id()==ID_struct) {
    exprt result=struct_exprt(real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();

    result.reserve_operands(components.size());
    for(struct_typet::componentst::const_iterator it=components.begin();
        it!=components.end();++it) {
      unsigned size=get_size(it->type());
      assert(size>=0);
      const exprt operand=get_value(it->type(), rhs, offset);
      offset += size;
      result.copy_to_operands(operand);
    }

    return result;
  } else if(real_type.id()==ID_array) {
    exprt result(ID_constant, type);
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));
    unsigned subtype_size=get_size(type.subtype());
    mp_integer mp_count;
    to_integer(size_expr, mp_count);
    unsigned count=integer2unsigned(mp_count);
    result.reserve_operands(count);
    for(unsigned i=0;i<count;i++) {
      const exprt operand=get_value(type.subtype(), rhs,
          offset+i * subtype_size);
      result.copy_to_operands(operand);
    }
    return result;
  } else if(real_type.id()==ID_floatbv) {
    ieee_floatt f;
    f.spec=to_floatbv_type(type);
    f.unpack(rhs[offset]);
    return f.to_expr();
  }
  else if(real_type.id()==ID_fixedbv)
  {
    fixedbvt f;
    f.from_integer(rhs[offset]);
    return f.to_expr();
  }
  else if(real_type.id()==ID_bool)
  {
    if(rhs[offset]!=0)
      return true_exprt();
    else
      return false_exprt();
  }
  else if((real_type.id()==ID_pointer) || (real_type.id()==ID_address_of))
  {
    if(rhs[offset]==0)
    {
      constant_exprt result(type);
      result.set_value(ID_NULL);
      return result;
    }
    if(rhs[offset]<memory.size())
    {
      memory_cellt &cell=memory[integer2unsigned(rhs[offset])];
      const typet type=get_type(cell.identifier);
      exprt symbol_expr(ID_symbol, type);
      symbol_expr.set(ID_identifier, cell.identifier);
      if(cell.offset==0) return address_of_exprt(symbol_expr);

      if(ns.follow(type).id()==ID_struct) {
        irep_idt member_id=get_component_id(cell.identifier,cell.offset);
        member_exprt member_expr(symbol_expr, member_id);
        return address_of_exprt(member_expr);
      }
      index_exprt index_expr(symbol_expr,
                             from_integer(cell.offset, integer_typet()));
      return index_expr;
    }
    message->error() << "pointer out of memory " << rhs[offset] << ">"
                    << memory.size() << messaget::endl << messaget::eom;
    throw "pointer out of memory";
  }
  return from_integer(rhs[offset], type);
}

/*******************************************************************

Function: interpretert::execute_assign

  Inputs:

 Outputs:

 Purpose: executes the assign statement at the current pc value

\*******************************************************************/

void interpretert::execute_assign()
{
  const code_assignt &code_assign=
    to_code_assign(PC->code);

  std::vector<mp_integer> rhs;
  evaluate(code_assign.rhs(), rhs);
  
  if(!rhs.empty())
  {
    mp_integer address=evaluate_address(code_assign.lhs()); 
    unsigned size=get_size(code_assign.lhs().type());

    if(size!=rhs.size())
      message->error() << "!! failed to obtain rhs (" << rhs.size() << " vs. "
                      << size << ")" << messaget::endl << messaget::eom;
    else
    {
      goto_trace_stept &trace_step=steps.get_last_step();
      assign(address, rhs);
      trace_step.full_lhs=code_assign.lhs();

      /* TODO: need to look at other cases on ssa_exprt 
       * (derference should be handled on ssa) */
      const exprt &expr=trace_step.full_lhs;
      if(ssa_exprt::can_build_identifier(trace_step.full_lhs))
      {
        trace_step.lhs_object=ssa_exprt(trace_step.full_lhs);
      }
      trace_step.full_lhs_value=get_value(trace_step.full_lhs.type(),rhs);
      trace_step.lhs_object_value=trace_step.full_lhs_value;
    }
  }
  else if(code_assign.rhs().id()==ID_side_effect)
  {
    side_effect_exprt side_effect=to_side_effect_expr(code_assign.rhs());
    if(side_effect.get_statement()==ID_nondet)
    {
      unsigned address=integer2unsigned(evaluate_address(code_assign.lhs()));
      unsigned size=get_size(code_assign.lhs().type());
      for (unsigned i=0;i<size;i++,address++)
      {
        memory[address].initialised=-1;
      }
    }
  }
}

/*******************************************************************\

Function: interpretert::assign

  Inputs:

 Outputs:

 Purpose: sets the memory at address with the given rhs value
          (up to sizeof(rhs))

\*******************************************************************/

void interpretert::assign(
  mp_integer address,
  const std::vector<mp_integer> &rhs)
{
  for(unsigned i=0;i<rhs.size();i++, ++address)
  {
    if(address<memory.size())
    {
      memory_cellt &cell=memory[integer2unsigned(address)];
      if(show) {
        message->status() << total_steps << " ** assigning " 
                          << cell.identifier << "["
                          << cell.offset << "]:=" << rhs[i] 
                          << messaget::endl << messaget::eom;
      }
      cell.value=rhs[i];
      if(cell.initialised==0) cell.initialised=1;
    }
  }
}

/*******************************************************************\

Function: interpretert::execute_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::execute_assume()
{
  if(!evaluate_boolean(PC->guard))
    throw "assumption failed";
}

/*******************************************************************\

Function: interpretert::execute_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::execute_assert()
{
  if(!evaluate_boolean(PC->guard))
  {
    if ((targetAssert==PC) || stop_on_assertion)
      throw "assertion failed";
    else if (show)
      message->error() << "assertion failed" 
                       << messaget::endl << messaget::eom;
  }
}

/*******************************************************************\

Function: interpretert::execute_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::execute_function_call()
{
  const code_function_callt &function_call=
    to_code_function_call(PC->code);

  // function to be called
  mp_integer a=evaluate_address(function_call.function());

  if(a==0)
    throw "function call to NULL";
  else if(a>=memory.size())
    throw "out-of-range function call";

  goto_trace_stept &trace_step=steps.get_last_step();
  const memory_cellt &cell=memory[integer2size_t(a)];
  const irep_idt &identifier=cell.identifier;
  trace_step.identifier=identifier;

  const goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(identifier);

  if(f_it==goto_functions.function_map.end())
    throw "failed to find function "+id2string(identifier);
    
  // return value
  mp_integer return_value_address;

  if(function_call.lhs().is_not_nil())
    return_value_address=
      evaluate_address(function_call.lhs());
  else
    return_value_address=0;
    
  // values of the arguments
  std::vector<std::vector<mp_integer>>argument_values;
  
  argument_values.resize(function_call.arguments().size());
  
  for(std::size_t i=0;i<function_call.arguments().size();i++)
    evaluate(function_call.arguments()[i], argument_values[i]);

  // do the call

  if(f_it->second.body_available())
  {
    call_stack.push(stack_framet());
    stack_framet &frame=call_stack.top();
    
    frame.return_PC=next_PC;
    frame.return_function=function;
    frame.old_stack_pointer=stack_pointer;
    frame.return_value_address=return_value_address;
    
    // local variables
    std::set<irep_idt> locals;
    get_local_identifiers(f_it->second, locals);
                    
    for(std::set<irep_idt>::const_iterator
        it=locals.begin();
        it!=locals.end();
        it++)
    {
      const irep_idt &id=*it;     
      const symbolt &symbol=ns.lookup(id);
      frame.local_map[id]=integer2unsigned(build_memory_map(id,symbol.type));

    }
        
    // assign the arguments
    const code_typet::parameterst &parameters=
      to_code_type(f_it->second.type).parameters();

    if(argument_values.size()<parameters.size())
      throw "not enough arguments";

    for(unsigned i=0;i<parameters.size();i++)
    {
      const code_typet::parametert &a=parameters[i];
      exprt symbol_expr(ID_symbol, a.type());
      symbol_expr.set(ID_identifier, a.get_identifier());
      assert(i<argument_values.size());
      assign(evaluate_address(symbol_expr), argument_values[i]);
    }

    // set up new PC
    function=f_it;
    next_PC=f_it->second.body.instructions.begin();   
  }
  else
  {
    list_input_varst::iterator it=
        function_input_vars.find(function_call.function().get(ID_identifier));
    if (it!=function_input_vars.end())
    {
      std::vector<mp_integer> value;
      assert(it->second.size()!=0);
      assert(it->second.front().return_assignments.size()!=0);
      evaluate(it->second.front().return_assignments.back().value,value);
      if (return_value_address>0)
      {
        assign(return_value_address,value);
      }
      if(function_call.lhs().is_not_nil())
      {
      }
      it->second.pop_front();
      return;
    }
    if (show)
      message->error() << "no body for "+id2string(identifier) 
                       << messaget::eom;
     /* TODO:used to be throw. need some better approach? 
      * need to check state of buffers (and by refs)    */
  }
}

/*******************************************************************\

Function: interpretert::build_memory_map

  Inputs:

 Outputs:

 Purpose: Creates a memory map of all static symbols in the program

\*******************************************************************/

void interpretert::build_memory_map()
{
  // put in a dummy for NULL
  memory.resize(1);
  memory[0].offset=0;
  memory[0].identifier="NULL-OBJECT";
  memory[0].initialised=0;

  num_dynamic_objects=0;
  dynamic_types.clear();

  // now do regular static symbols
  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
    build_memory_map(it->second);
    
  // for the locals
  stack_pointer=memory.size();
}

/*******************************************************************\

Function: interpretert::build_memory_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::build_memory_map(const symbolt &symbol)
{
  unsigned size=0;

  if(symbol.type.id()==ID_code)
  {
    size=1;
  }
  else if(symbol.is_static_lifetime)
  {
    size=get_size(symbol.type);
  }

  if(size!=0)
  {
    unsigned address=memory.size();
    memory.resize(address+size);
    memory_map[symbol.name]=address;
    
    for(unsigned i=0;i<size;i++)
    {
      memory_cellt &cell=memory[address+i];
      cell.identifier=symbol.name;
      cell.offset=i;
      cell.value=0;
      cell.initialised=0;
    }
  }
}

/*******************************************************************\

Function: interpretert::concretise_type

  Inputs:

 Outputs:

 Purpose: turns a variable length array type into a fixed array type 

\*******************************************************************/
typet interpretert::concretise_type(const typet &type) const
{
  if(type.id()==ID_array)
  {
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));
    std::vector<mp_integer> computed_size;
    evaluate(size_expr,computed_size);
    if(computed_size.size()==1 &&
       computed_size[0]>=0)
    {
      message->result() << "Concretised array with size " << computed_size[0] 
                        << messaget::eom;
      return array_typet(type.subtype(),
             constant_exprt::integer_constant(computed_size[0].to_ulong()));
    }
    else {
      message->error() << "Failed to concretise variable array" 
                       << messaget::eom;
    }
  }
  return type;
}

/*******************************************************************\

Function: interpretert::build_memory_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
mp_integer interpretert::build_memory_map(const irep_idt &id,
                                          const typet &type) const
{
  typet alloc_type=concretise_type(type);
  unsigned size=get_size(alloc_type);
  std::map<const irep_idt,const typet>::iterator it = dynamic_types.find(id);

  if (it!=dynamic_types.end()) {
    int offset=1;

    unsigned address = memory_map[id];

    while (memory[address+offset].offset>0) offset++;

    // current size <= size already recorded
    if(size<=offset) 
      return memory_map[id];

  }

  /* the current size is bigger then the one previously recorded
   * in the memory map */
  
  if(size==0) size=1;// This is a hack to create existence

  if(size!=0)
  {
    unsigned address=memory.size();
    memory.resize(address+size);
    memory_map[id]=address;
    dynamic_types.insert(std::pair<const irep_idt,typet>(id,alloc_type));

    for(unsigned i=0;i<size;i++)
    {
      memory_cellt &cell=memory[address+i];
      cell.identifier=id;
      cell.offset=i;
      cell.value=0;
      cell.initialised=0;
    }
    return address;
  }

  return 0;
}

/*******************************************************************\

Function: interpretert::get_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned interpretert::get_size(const typet &type) const
{
  if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    unsigned sum=0;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &sub_type=it->type();

      if(sub_type.id()!=ID_code)
        sum+=get_size(sub_type);
    }
    
    return sum;
  }
  else if(type.id()==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    unsigned max_size=0;

    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &sub_type=it->type();

      if(sub_type.id()!=ID_code)
        max_size=std::max(max_size, get_size(sub_type));
    }

    return max_size;   
  }
  else if(type.id()==ID_array)
  {
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));

    unsigned subtype_size=get_size(type.subtype());

    std::vector<mp_integer> i;
    evaluate(size_expr,i);
    if(i.size()==1)
    {
      // Go via the binary representation to reproduce any
      // overflow behaviour.
      exprt size_const=from_integer(i[0],size_expr.type());
      mp_integer size_mp;
      assert(!to_integer(size_const,size_mp));
      return subtype_size*integer2unsigned(size_mp);
    }
    else
      return subtype_size;
  }
  else if(type.id()==ID_symbol)
  {
    return get_size(ns.follow(type));
  }
    return 1;
}

/*******************************************************************

Function: list_non_bodied

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::list_non_bodied() {
  int funcs=0;
  function_input_vars.clear();
  for(goto_functionst::function_mapt::const_iterator f_it =
       goto_functions.function_map.begin();
       f_it!=goto_functions.function_map.end(); f_it++)
  {
    if(f_it->second.body_available()) 
    {
      list_non_bodied(f_it->second.body.instructions);
    }
  }

  message->result() << "non bodied varibles " << funcs << messaget::eom;
  std::map<const irep_idt,const irep_idt>::const_iterator it;
/*for(it=function_input_vars.begin(); it!=function_input_vars.end(); it++)
  {
    message->result() << it->first << "=" 
                      << it->second.front() << messaget::endl;
  }*/
  message->result() << messaget::eom;
}

char interpretert::is_opaque_function(
                   const goto_programt::instructionst::const_iterator &it,
                   irep_idt &id)
{
  goto_programt::instructionst::const_iterator pc=it;
  if (pc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(pc->code);
    if(code_assign.rhs().id()==ID_side_effect)
    {
      side_effect_exprt side_effect=to_side_effect_expr(code_assign.rhs());
      if(side_effect.get_statement()==ID_nondet)
      {
        pc--;//TODO: need to check if pc is not already at begin
        if(pc->is_return()) pc--;
      }
    }
  }
  if(pc->type!=FUNCTION_CALL) return 0;
  const code_function_callt &function_call=to_code_function_call(pc->code);
  id=function_call.function().get(ID_identifier);
  const goto_functionst::function_mapt::const_iterator f_it=goto_functions.function_map.find(id);
  if(f_it==goto_functions.function_map.end())
    throw "failed to find function "+id2string(id);
  if(f_it->second.body_available()) return 0;
  if(function_call.lhs().is_not_nil()) return 1;
  return -1;
}

void interpretert::list_non_bodied(
                   const goto_programt::instructionst &instructions)
{
  for(goto_programt::instructionst::const_iterator f_it =
    instructions.begin(); f_it!=instructions.end(); f_it++) 
  {
    irep_idt f_id;
    if(is_opaque_function(f_it,f_id)>0)
    {
      const code_assignt &code_assign=to_code_assign(f_it->code);
      unsigned return_address=
                 integer2unsigned(evaluate_address(code_assign.lhs()));
      if((return_address > 0) && (return_address<memory.size()))
      {
        function_assignmentt retval=
            {irep_idt(), get_value(code_assign.lhs().type(),return_address)};
        function_assignmentst defnlist={ retval };
        /* Add an actual calling context instead of a blank irep if our
         * caller needs it.*/
        function_input_vars[f_id].push_back({irep_idt(), defnlist});
      }
    }
  }
}

/*******************************************************************

Function: fill_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::fill_inputs(input_varst &inputs) 
{
  for(input_varst::iterator it=inputs.begin(); it!=inputs.end(); it++)
  {
    std::vector<mp_integer > rhs;
    evaluate(it->second, rhs);
    if(rhs.empty()) continue;
    memory_mapt::const_iterator m_it1=memory_map.find(it->first);
    if(m_it1==memory_map.end()) continue;
    mp_integer address=m_it1->second;
    unsigned size=get_size(it->second.type());
    if(size!=rhs.size()) continue;
    assign(address, rhs);
  }
  clear_input_flags();
}

/*******************************************************************
 Function: list_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::list_inputs(bool use_non_det) {
  input_vars.clear();
  for(unsigned long i=0;i<memory.size();i++) {
    const memory_cellt &cell=memory[i];
    if(cell.initialised>=0)
      continue;
    if(strncmp(cell.identifier.c_str(), "__CPROVER", 9)==0)
      continue;

    try {
      typet symbol_type=get_type(cell.identifier);
      if(use_non_det) {
        exprt value=get_value(symbol_type, i - cell.offset);
        input_vars.insert(
            std::pair<irep_idt, exprt>(cell.identifier, value));
      } else {
        std::vector<mp_integer> rhs;
        while(memory[i].offset>0)
          i--;
        rhs.push_back(memory[i].value);
        for(unsigned long j=i+1;j<memory.size();j++) {
          const memory_cellt &cell=memory[j];
          if(cell.offset==0)
            break;
          rhs.push_back(cell.value);
        }
        exprt value=get_value(symbol_type, rhs);
        input_vars.insert(
            std::pair<irep_idt, exprt>(cell.identifier, value));
      }
    } catch (const char *e) {
    } catch (const std::string e) {
    }
    for(unsigned long j=i+1;
        (j<memory.size() && memory[j].offset!=0);j++)
      i++;
  }
}

/*******************************************************************
 Function: list_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::list_inputs(input_varst &inputs) {
  input_vars.clear();
  for(unsigned long i=0;i<memory.size();i++) {
    const memory_cellt &cell=memory[i];
    if(cell.initialised>=0) continue;
    if (strncmp(cell.identifier.c_str(), "__CPROVER", 9)==0) continue;
    if(inputs.find(cell.identifier)!=inputs.end())
    {
      input_vars[cell.identifier]=inputs[cell.identifier];
    }
    unsigned j=i+1;
    while((j<memory.size()) && (memory[j].offset>0)) j++;
    i=j-1;
  }
  for (input_varst::iterator it=inputs.begin();it!=inputs.end();it++)
  {
    if ((it->second.type().id()==ID_pointer) && (it->second.has_operands()))
    {
      const exprt& op=it->second.op0();
      if((op.id()==ID_address_of) && (op.has_operands()))
      {
        mp_integer address=evaluate_address(op.op0());
        irep_idt id=memory[integer2unsigned(address)].identifier;
        if(strncmp(id.c_str(),"symex_dynamic::dynamic_object",28)==0)
        {
          input_vars[it->first]=inputs[it->first];
        }
      }
    }
  }
}

/*******************************************************************
 Function: print_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::print_inputs() {
  if(input_vars.size()<=0)
    list_inputs();
  for(input_varst::iterator it=input_vars.begin();it!=input_vars.end();
      it++) {
    message->result() << it->first << "=" 
                      << from_expr(ns, it->first, it->second) << "[" 
                      << it->second.type().id() << "]" << messaget::eom;
  }
  message->result() << messaget::eom;
}

/*******************************************************************
 Function: print_memory

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::print_memory(bool input_flags) {
  for(unsigned i=0;i<memory.size();i++)
  {
    memory_cellt &cell=memory[i];
    message->debug() << cell.identifier << "[" << cell.offset << "]"
            << "=" << cell.value << messaget::eom;
    if(input_flags) message->debug() << "(" << (int)cell.initialised << ")" 
                                     << messaget::eom;
    message->debug() << messaget::eom;
  }
}

/*******************************************************************
 Function: getPC

 Inputs:

 Outputs:

 Purpose: retrieves the PC pointer for the given location

 \*******************************************************************/
goto_programt::const_targett interpretert::getPC(const unsigned location,
                                                 bool &ok)
{
  goto_programt::const_targett no_location;
  for(goto_functionst::function_mapt::const_iterator f_it =
      goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end(); f_it++)
  {
    if(f_it->second.body_available())
    {
      for(goto_programt::instructionst::const_iterator it =
          f_it->second.body.instructions.begin();
          it!=f_it->second.body.instructions.end(); it++)
      {
        if (it->location_number==location)
        {
          ok=true;
          return it;
        }
      }
    }
  }
  ok=false;
  return no_location;
}

/*******************************************************************
 Function: prune_inputs

 Inputs:

 Outputs:

 Purpose: cleans the list of inputs organising std vectors into arrays and filtering non-inputs if requested

 \*******************************************************************/
void interpretert::prune_inputs(input_varst &inputs,
                                list_input_varst& function_inputs,
                                const bool filter)
{
  for(list_input_varst::iterator it=function_inputs.begin();
      it!=function_inputs.end();it++) 
  {
    const exprt size=from_integer(it->second.size(), integer_typet());
    assert(it->second.front().return_assignments.size()!=0);
    const auto& first_function_assigns=it->second.front().return_assignments;
    const auto& toplevel_definition=first_function_assigns.back().value;
    array_typet type=array_typet(toplevel_definition.type(),size);
    array_exprt list(type);
    list.reserve_operands(it->second.size());
    for(auto l_it : it->second)
    {
      list.copy_to_operands(l_it.return_assignments.back().value);
    }
    inputs[it->first]=list;
  }
  input_vars=inputs;
  function_input_vars=function_inputs;
  if(filter)
  {
    try
    {
      fill_inputs(inputs);
      while(!done) {
        show_state();
        step();
      }
    }
    catch (const char *e)
    {
      message->error() << e << messaget::eom;
    }
    list_inputs();
    list_inputs(inputs);
  }
}

/*******************************************************************
 Function: load_counter_example_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

interpretert::input_varst& interpretert::load_counter_example_inputs(
    const std::string &filename) {
  jsont counter_example;
  message_clientt message_client;

  if(parse_json(filename,message_client.get_message_handler(),counter_example))
  {
    bool ok;
    show=false;
    stop_on_assertion=false;

    input_varst inputs;
    list_input_varst function_inputs;

    function=goto_functions.function_map.find(goto_functionst::entry_point());
    if(function==goto_functions.function_map.end())
      throw "main not found";

    initialise(true);
    jsont::objectt::const_reverse_iterator it=counter_example.object.rbegin();
    if(it!=counter_example.object.rend())
    {
      unsigned location=
               integer2unsigned(string2integer(it->second["location"].value));
      targetAssert=getPC(location,ok);
    }

    while(it!=counter_example.object.rend())
    {
      const jsont &pc_object=it->second["location"];
      if (pc_object.kind==jsont::J_NULL) continue;
      unsigned location=integer2unsigned(string2integer(pc_object.value));
      goto_programt::const_targett pc=getPC(location,ok);
      if (!ok) continue;
      const jsont &lhs_object=it->second["lhs"];
      if (lhs_object.kind==jsont::J_NULL) continue;
      irep_idt id=lhs_object.value;
      const jsont &val_object=it->second["value"];
      if (val_object.kind==jsont::J_NULL) continue;
      if(pc->is_other() || pc->is_assign() || pc->is_function_call())
      {
        const code_assignt &code_assign=to_code_assign(PC->code);
        //TODO: the other and function_call may be different
        mp_integer address;
        const exprt &lhs=code_assign.lhs();
        exprt value=to_expr(ns, id, val_object.value);
        symbol_exprt symbol_expr=to_symbol_expr(
            (lhs.id()==ID_member) ? to_member_expr(lhs).symbol() : lhs);
        irep_idt id=symbol_expr.get_identifier();
        address=evaluate_address(lhs);
        if(address==0) {
          address=build_memory_map(id,symbol_expr.type());
        }
        std::vector<mp_integer> rhs;
        evaluate(value,rhs);
        assign(address, rhs);
        if(lhs.id()==ID_member)
        {
          address=evaluate_address(symbol_expr);
          inputs[id]=get_value(symbol_expr.type(),integer2unsigned(address));
        }
        else
        {
          inputs[id]=value;
        }
        irep_idt f_id;
        if(is_opaque_function(pc,f_id)!=0)
        {
          // TODO: save/restore the full data structure?
          function_inputs[f_id].push_front({ irep_idt(), 
                                         { { irep_idt(), inputs[id] } } });
        }
      }
      it++;
    }
    prune_inputs(inputs,function_inputs,true);
    print_inputs();
    show=true;
    stop_on_assertion=true;
  }
  return input_vars;
}

/*******************************************************************
 Function: get_assigned_symbol

 Inputs: Trace step

 Outputs: Symbol expression that the step assigned to

 Purpose: Looks through memberof expressions etc to find a root symbol.

 \*******************************************************************/

static symbol_exprt get_assigned_symbol(const exprt& expr)
{
  if(expr.id() == ID_symbol)
    return to_symbol_expr(expr);

  if(expr.id() == ID_member ||
     expr.id() == ID_dereference ||
     expr.id() == ID_typecast ||
     expr.id() == ID_index ||
     expr.id() == ID_byte_extract_little_endian ||
     expr.id() == ID_byte_extract_big_endian)
    return get_assigned_symbol(expr.op0());

  // Try to handle opcodes I haven't thought of by looking for the
  // only pointer-typed operand:

  const exprt* unique_pointer = 0;
  
  for(const auto& op : expr.operands())
  {
    if(op.type().id() == ID_pointer)
    {
      if(!unique_pointer)
    unique_pointer = &op;
      else
      {
    unique_pointer = 0;
    break;
      }
    }
  }

  if(unique_pointer)
    return get_assigned_symbol(*unique_pointer);
  else
  {
    std::string error = "Failed to look through '" + as_string(expr.id())
      + "' in get_assigned_symbol.";
    throw error;
  }
}

static symbol_exprt get_assigned_symbol(const goto_trace_stept& step)
{
  return get_assigned_symbol(step.full_lhs);
}

/*******************************************************************
 Function: calls_opaque_stub

 Inputs: Call instruction and symbol table

 Outputs: Returns COMPLEX_OPAQUE_STUB if the given instruction
          calls a function with a synthetic stub modelling its
          behaviour, or SIMPLE_OPAQUE_STUB if it is not available at all,
          or NOT_OPAQUE_STUB otherwise.
          In the first case, sets capture_symbol to the symbol name
          the stub defines. In either stub case, sets f_id to the function
          called.

 Purpose: Determine whether a call instruction targets an internal
          function or some form of opaque function.

 \*******************************************************************/



bool calls_opaque_stub(const code_function_callt& callinst,
  const symbol_tablet& symbol_table, irep_idt& f_id, irep_idt& capture_symbol)
{
  f_id=callinst.function().get(ID_identifier);
  const symbolt& called_func=symbol_table.lookup(f_id);
  capture_symbol=called_func.type.get("opaque_method_capture_symbol");
  if(capture_symbol!=irep_idt())
    return true;
  else
    return false;
}

/*******************************************************************
 Function: get_value_tree

 Inputs: Symbol to capture, map of current symbol ("input") values.

 Outputs: Populates captured with a top-down-ordered list of symbol
          values containing every value reachable from capture_symbol.
          For example, if capture_symbol contains a pointer to some
          object x, captured will be populated with x's value and then
          capture_symbol's.

 Purpose: Take a snapshot of state reachable from capture_symbol.

 \*******************************************************************/

// Get the current value of capture_symbol plus
// the values of any symbols referenced in its fields.
// Store them in 'captured' in bottom-up order.
void interpretert::get_value_tree(const irep_idt& capture_symbol,
                  function_assignmentst& captured)
{

  // Circular reference?
  for(auto already_captured : captured)
    if(already_captured.id==capture_symbol)
      return;
  exprt defined=get_value(capture_symbol);

  captured.push_back({capture_symbol, defined});

  if(defined.type().id()==ID_pointer)
  {
    get_value_tree(defined,captured);
  }
  else if(defined.type().id()==ID_struct ||
      defined.type().id()==ID_array)
  {
    /* Assumption: all object trees captured this way refer directly 
     * to particular symex::dynamic_object expressions, which are always
     * address-of-symbol constructions.*/
    forall_operands(opit, defined) {
      if(opit->type().id()==ID_pointer)
        get_value_tree(*opit,captured);
    }
  }
  else
  {
    // Primitive, just capture this.
  }

}

void interpretert::get_value_tree(const exprt& capture_expr,
                  function_assignmentst& captured)
{
  assert(capture_expr.type().id()==ID_pointer);
  if(capture_expr!=null_pointer_exprt(to_pointer_type(capture_expr.type())))
  {
    const auto& referee=to_symbol_expr(
                to_address_of_expr(capture_expr).object()).get_identifier();
    get_value_tree(referee,captured);
  }
}

// Wrapper for above, giving bottom-up ordering
void interpretert::get_value_tree_bu(const irep_idt& capture_symbol,
                                     function_assignmentst& captured)
{
  get_value_tree(capture_symbol,captured);
  std::reverse(captured.begin(),captured.end());
}
                                  

static bool is_assign_step(const goto_trace_stept& step)
{
  return goto_trace_stept::ASSIGNMENT==step.type
    && (step.pc->is_other() || step.pc->is_assign()
        || step.pc->is_function_call());
}

static bool is_constructor_call(const goto_trace_stept& step,
                const symbol_tablet& st)
{
  const auto& call=to_code_function_call(step.pc->code);
  const auto& id=call.function().get(ID_identifier);
  auto callee_type=st.lookup(id).type;
  return callee_type.get_bool(ID_constructor);
}

struct trace_stack_entry {
  irep_idt func_name;
  mp_integer this_address;
  irep_idt capture_symbol;
  bool is_super_call;
  std::vector<interpretert::function_assignmentt> param_values;
};

static bool is_super_call(const trace_stack_entry& called,
                          const trace_stack_entry& caller)
{
  // If either call isn't an instance method, it's not a super call:
  if(called.this_address==0 || caller.this_address==0)
    return false;

  // If the this-addresses don't match, it's not a super call:
  if(called.this_address!=caller.this_address)
    return false;
  
  /* If the names (including class) match entirely, 
   * this is simply a recursive call:*/
  if(called.func_name == caller.func_name)
    return false;

  // Check whether the mangled method names (disregarding class) match:
  std::string calleds=as_string(called.func_name);
  std::string callers=as_string(caller.func_name);
  size_t calledoff=calleds.rfind('.'), calleroff=callers.rfind('.');
  if(calledoff==std::string::npos || calleroff==std::string::npos)
    return false;
  return calleds.substr(calledoff)==callers.substr(calleroff);
}

mp_integer interpretert::get_this_address(const code_function_callt& call_code)
{
  if(!to_code_type(call_code.function().type()).has_this())
    return 0;
  
  std::vector<mp_integer> this_address;
  assert(call_code.arguments().size()!=0);
  evaluate(call_code.arguments()[0],this_address);
  if(this_address.size()==0)
  {
    message->warning() << "Failed to evaluate this-arg for " <<
      from_expr(ns,"",call_code.function()) << messaget::eom;
    return 0;
  }
  assert(this_address.size()==1);
  return this_address[0];
}

exprt interpretert::get_value(const irep_idt& id)
{
  // The dynamic type and the static symbol type may differ for VLAs,
  // where the symbol carries a size expression and the dynamic type
  // registry contains its actual length.
  auto findit=dynamic_types.find(id);
  typet get_type;
  if(findit!=dynamic_types.end())
    get_type=findit->second;
  else
    get_type=symbol_table.lookup(id).type;
  
  symbol_exprt symbol_expr(id,get_type);
  mp_integer whole_lhs_object_address=evaluate_address(symbol_expr);

  return get_value(get_type,integer2unsigned(whole_lhs_object_address));
}

const exprt & get_entry_function(const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &fm=gf.function_map;
  const irep_idt start(goto_functionst::entry_point());
  const function_mapt::const_iterator entry_func=fm.find(start);
  assert(fm.end() != entry_func);
  const goto_programt::instructionst &in=entry_func->second.body.instructions;
  typedef goto_programt::instructionst::const_reverse_iterator reverse_target;
  reverse_target codeit=in.rbegin();
  const reverse_target end=in.rend();
  assert(end != codeit);
  // Tolerate 'dead' statements at the end of _start.
  while(end!=codeit && codeit->code.get_statement()!=ID_function_call)
    ++codeit;
  assert(end != codeit);
  const reverse_target call=codeit;
  const code_function_callt &func_call=to_code_function_call(call->code);
  const exprt &func_expr=func_call.function();
  return func_expr;
}


/*******************************************************************
 Function: load_counter_example_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

interpretert::input_varst& interpretert::load_counter_example_inputs(
     const goto_tracet &trace, list_input_varst& function_inputs,
     side_effects_differencet &valuesDifference, const bool filtered)
{
  show=false;
  stop_on_assertion=false;

  input_varst inputs;

  function=goto_functions.function_map.find(goto_functionst::entry_point());
  if(function==goto_functions.function_map.end())
    throw "main not found";

  irep_idt previous_assigned_symbol;
 
  initialise(false);

  // First walk the trace forwards to initialise variable-length arrays
  // whose size-expressions depend on context (e.g. int x = 5; int[] y = new int[x];)
  // We also take the opportunity to save the results of evaluate_address and evaluate
  // such that any non-constant expressions (e.g. the occasional byte_extract(..., i, ...)
  // creeps in that needs the current value of local 'i') will be evaluated correctly.

  std::vector<std::pair<mp_integer, std::vector<mp_integer> > > trace_eval;
  std::vector<trace_stack_entry> trace_stack;
  int outermost_constructor_depth=-1;
  int expect_parameter_assignments=0;

  trace_stack.push_back(
        {goto_functionst::entry_point(),0,irep_idt(),false,{}});

  const exprt &func_expr = get_entry_function(goto_functions);
  const irep_idt &func_name = to_symbol_expr(func_expr).get_identifier();
  const code_typet::parameterst &params=
                    to_code_type(func_expr.type()).parameters();

  std::map<std::string, const irep_idt &> parameterSet;

  // mapping <structure, field> -> value
  std::map<std::pair<const irep_idt,const irep_idt>,const exprt> valuesBefore;

  namespacet ns(symbol_table);

  for(const auto &p : params)
    parameterSet.insert({id2string(p.get_identifier()), p.get_identifier()});
  
  for(auto it=trace.steps.begin(),itend=trace.steps.end();it!=itend;++it)
  {
    const auto& step=*it;
    if(is_assign_step(step))
    {
      mp_integer address;
      symbol_exprt symbol_expr=get_assigned_symbol(step);
      irep_idt id=symbol_expr.get_identifier();

      #ifdef DEBUG
      message->status() << it->pc->function << ": " 
                        << from_expr(ns,"",step.full_lhs) 
                        << " <- " << from_expr(ns,"",step.full_lhs_value)
                        << messaget::eom;
      #endif

      address=evaluate_address(step.full_lhs);
      if(address==0)
        address=build_memory_map(id,symbol_expr.type());

      std::vector<mp_integer> rhs;
      evaluate(step.full_lhs_value,rhs);
      if(rhs.size()==0)
      {
        evaluate(step.full_lhs,rhs);
        if(rhs.size()!=0)
        {
          message->warning() << "symex::build_goto_trace couldn't evaluate this expression, but the interpreter could." << messaget::eom;
        }
      }
      assign(address,rhs);

      if(expect_parameter_assignments!=0)
      {
        if(!--expect_parameter_assignments)
        {
          /* Just executed the last parameter assignment for a function
           * we just entered.
           * Capture the arguments of *every* call as it is entered,
           * because we might need them for verification if it happens
           * to call a super-method later.*/
          std::vector<function_assignmentt> actual_params;
          const auto& this_function=trace_stack.back().func_name;
          const auto& formal_params=
            to_code_type(symbol_table.lookup(this_function).type).parameters();
          std::vector<function_assignmentt> direct_params;
          bool is_constructor=
               id2string(this_function).find("<init>")!=std::string::npos;
      
          for(const auto& fp : formal_params)
          {
            /* Don't capture 'this' on entering a constructor, as it's
             * uninitialised at this point. */
            if(is_constructor && fp.get_this())
              continue;
            /* Note this will record the actual parameter values as well as
             * anything reachable from them. We use a single actual_params
             * list for all parameters to avoid redundancy e.g. if parameters
             * or objects reachable from them alias, we only need to capture
             * that subtree once.*/
            get_value_tree_bu(fp.get_identifier(),actual_params);
            /* Set the actual direct params aside, so we can keep them in
             * order at the back.*/
            direct_params.push_back(std::move(actual_params.back()));
            actual_params.pop_back();
          }

          // Put the direct params back on the end of the list:
          actual_params.insert(actual_params.end(),direct_params.begin(),
                               direct_params.end());
#ifdef DEBUG
          for(const auto& id_expr : actual_params)
            message->status() << "Param " << id_expr.id << " = " <<
              from_expr(ns,"",id_expr.value) << messaget::eom;
#endif
          trace_stack.back().param_values=std::move(actual_params);

        }
      }

      trace_eval.push_back(std::make_pair(address, rhs));

      /********* 8< **********/
      irep_idt identifier=step.lhs_object.get_identifier();
      auto param = parameterSet.find(id2string(identifier));
      if(param != parameterSet.end())
      {
        const exprt &expr = step.full_lhs_value;
        interpretert::function_assignmentst input_assigns;
        get_value_tree(identifier, input_assigns);
        for(const auto &assign : input_assigns)
        {
          const typet &tree_typ = ns.follow(assign.value.type());
          if(tree_typ.id()==ID_struct)
          {
            const struct_typet &struct_type=to_struct_type(tree_typ);
            const struct_typet::componentst &components=
                                             struct_type.components();
            const struct_exprt &struct_expr=to_struct_expr(assign.value);
            const auto& ops=struct_expr.operands();
            for(size_t fieldidx=0,fieldlim=ops.size();
                fieldidx!=fieldlim;++fieldidx)
            {
              const exprt & expr = ops[fieldidx];
              // only look at atomic types for now
              if(expr.type().id()==ID_signedbv ||
                 expr.type().id()==ID_c_bool)
              {
                valuesBefore.insert({{assign.id, 
                                     components[fieldidx].get_name()}, expr});
              }
            }
          }
        }
      }
      /********* 8< **********/
    }
    else if(step.is_function_call())
    {
      irep_idt called, capture_symbol;
      bool is_cons=is_constructor_call(step,symbol_table);
      // No need to intercept j.l.O's constructor since we know it doesn't do
      // anything visible to the object's state.
      // TODO: consider just supplying a constructor for it?
      auto is_stub=calls_opaque_stub(to_code_function_call(step.pc->code),
                                     symbol_table,called,capture_symbol);
      bool is_jlo_cons=is_cons &&
           as_string(called).find("java.lang.Object")!=std::string::npos;

      mp_integer this_address=
                 get_this_address(to_code_function_call(step.pc->code));

      trace_stack.push_back({called,this_address,irep_idt(),false,{}});

      assert(expect_parameter_assignments==0 &&
             "Entered another function before the parameter assignment chain was done?");
      // Capture upcoming parameter assignments:
      expect_parameter_assignments=
        to_code_type(to_code_function_call(step.pc->code).function().type()).parameters().size();
      
      bool is_super=(!is_cons) && trace_stack.size()!=0 &&
           is_super_call(trace_stack.back(),trace_stack[trace_stack.size()-2]);
      trace_stack.back().is_super_call=is_super;
      
      if((!is_stub) || is_jlo_cons)
      {
    if(is_cons)
    {
      if(outermost_constructor_depth==-1)
        outermost_constructor_depth=trace_stack.size()-1;
    }
    else
      outermost_constructor_depth=-1;
      }
      else
      {
    /* Capture the value of capture_symbol instead of whatever happened
     * to have been defined most recently. Also capture any other referenced
     * objects.
     * Capture after the stub finishes, or in the particular case of a
     * constructor that makes opaque super-calls, after the outermost
     * constructor finishes.*/
    if(is_cons && outermost_constructor_depth!=-1)
    {
      assert(outermost_constructor_depth < trace_stack.size());
      trace_stack[outermost_constructor_depth].capture_symbol=capture_symbol;
    }
    else if(trace_stack.back().is_super_call)
    {
      /* When a method calls the overridden method, capture the return value
       * of the child method, as replacing the supercall is tricky using
       * mocking tools.
       * We could also consider generating a new method that can be stubbed.*/
      auto findit=trace_stack.rbegin();
      while(findit!=trace_stack.rend() && findit->is_super_call)
        ++findit;
      assert(findit!=trace_stack.rend());
      assert(findit->capture_symbol==irep_idt() 
             && "Stub somehow called a super-method?");
      findit->capture_symbol=as_string(findit->func_name)+RETURN_VALUE_SUFFIX;
    }
    else
      trace_stack.back().capture_symbol=capture_symbol;
    outermost_constructor_depth=-1;
      }
    }
    else if(step.is_function_return())
    {
      outermost_constructor_depth=-1;
      assert(trace_stack.size()>=1);
      assert(expect_parameter_assignments==0 &&
        "Exited function before the parameter assignment chain was done?");
      const auto& ret_func=trace_stack.back();
      if(ret_func.capture_symbol!=irep_idt())
      {
        assert(trace_stack.size()>=2);
    // We must record the value of stub_capture_symbol now.
    function_assignmentst defined;
    get_value_tree_bu(ret_func.capture_symbol,defined);
    if(defined.size()!=0) // Definition found?
    {
      const auto& caller=trace_stack[trace_stack.size()-2].func_name;
      function_inputs[ret_func.func_name].push_back({
        caller,std::move(defined),std::move(trace_stack.back().param_values)});
    }
      }
      trace_stack.pop_back();
    }
    else if(step.type==goto_trace_stept::OUTPUT)
    {
      for(const auto &inputParam : parameterSet)
      {
        std::size_t found = (inputParam.first).rfind(id2string(step.io_id));
        if(found!=std::string::npos)
        {
          /* looping over io_args will ignore atomic types which won't have
           * side effects*/
          interpretert::function_assignmentst output_assigns;
          get_value_tree(inputParam.second, output_assigns);
          const typet &typ = symbol_table.lookup(inputParam.second).type;
          for(const auto &assign : output_assigns)
          {
            const typet &tree_typ = ns.follow(assign.value.type());
            if(tree_typ.id()==ID_struct)
            {
              const struct_typet &struct_type=to_struct_type(tree_typ);
              const struct_typet::componentst &components=
                                               struct_type.components();
              const struct_exprt &struct_expr=to_struct_expr(assign.value);
              const auto& ops=struct_expr.operands();
              for(size_t fieldidx=0, fieldlim=ops.size();
                  fieldidx!=fieldlim;fieldidx++)
              {
                const exprt &after_expr = ops[fieldidx];
                if(after_expr.type().id()==ID_signedbv ||
                   after_expr.type().id()==ID_c_bool)
                   // after_expr.type().id()==ID_string ||
                   // after_expr.type().id()==ID_floatbv)
                {
                  auto findit=valuesBefore.find({assign.id, 
                                    components[fieldidx].get_name()});
                  if(findit!=valuesBefore.end())
                  {
                    const exprt &before_expr = findit->second;
                    assert(after_expr.type().id()==before_expr.type().id());
                    mp_integer a, b;
                    to_integer(after_expr, a);
                    to_integer(before_expr, b);
                    if (a != b)
                    {
                      valuesDifference.insert({{assign.id,
                            components[fieldidx].get_name()},
                            {before_expr, after_expr}});
                    }
                  }
                  //TODO: decide what to do when a field wasn't reachable before
                  // (e.g. inaccessible due to a null pointer)
                }
              }
            }
          }
        }
      }
    }
  }

  // Now walk backwards to find object states on entering 'main'.
  // TODO integrate this into the forwards walk as well.

  auto trace_eval_iter=trace_eval.rbegin();
  goto_tracet::stepst::const_reverse_iterator it=trace.steps.rbegin();
  if(it!=trace.steps.rend()) targetAssert=it->pc;
  for(;it!=trace.steps.rend();++it) {
    if(is_assign_step(*it))
    {

      assert(trace_eval_iter!=trace_eval.rend() &&
             "Assign steps failed to line up between fw and bw passes?");
      const auto& eval_result=*(trace_eval_iter++);
      const auto& address=eval_result.first;
      const auto& rhs=eval_result.second;

      assert(address!=0);
      assign(address,rhs);

      symbol_exprt symbol_expr=get_assigned_symbol(*it);
      irep_idt id=symbol_expr.get_identifier();

      inputs[id]=get_value(id);
      input_first_assignments[id]=it->pc->function;
    }
  }

  assert(trace_eval_iter==trace_eval.rend() &&
         "Backward interpreter walk didn't consume all eval entries?");
  
  prune_inputs(inputs,function_inputs,filtered);
  print_inputs();
  show=true;
  stop_on_assertion=true;
  return input_vars;
}

/*******************************************************************

Function: interpreter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpreter(
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  messaget *message_handler)
{
  interpretert interpreter(symbol_table,goto_functions,
                           message_handler,optionst());
  interpreter();
}
