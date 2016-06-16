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
#include <ansi-c/c_types.h>
#include <json/json_parser.h>

#include "interpreter.h"
#include "interpreter_class.h"

/*******************************************************************\

Function: interpretert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::operator()()
{
  show=true;
  initialise(true);
  try {
    std::cout << "Initialize:";

    std::cout << "Type h for help" << std::endl;
    while(!done) {
      num_steps=1;
      stack_depth=-1;
      command();
      if(num_steps==0)
        show_state();
      while(!done && ((num_steps<0) || ((num_steps--)>0))) {
        step();
        show_state();
      }
      while(!done && (stack_depth<=call_stack.size())
         && (stack_depth>=0)) {
        step();
        show_state();
      }
    }
    std::cout << "Program End." << std::endl;
  } catch (const char *e) {
    std::cout << e << std::endl;
  }
  while(!done) command();
}

/*******************************************************************

Function: interpretert::initialise

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void interpretert::initialise(bool init) {
  build_memory_map();
  
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
    while(!done && (stack_depth<=call_stack.size()) && (stack_depth>=0)) {
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

 Purpose:

\*******************************************************************/

void interpretert::show_state()
{
  if(!show) return;
  std::cout << std::endl;
  std::cout << "----------------------------------------------------"
            << std::endl;

  if(PC==function->second.body.instructions.end())
  {
    std::cout << "End of function `"
              << function->first << "'" << std::endl;
  }
  else
    function->second.body.output_instruction(ns, function->first, std::cout, PC);
}

/*******************************************************************\

Function: interpretert::command

  Inputs:

 Outputs:

 Purpose:

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
  else if(ch=='h') {
    num_steps=0;
    std::cout << "Interpreter help" << std::endl;
    std::cout << "h: display this menu" << std::endl;
    std::cout << "i: output program inputs" << std::endl;
    std::cout << "id: output program inputs with det values for don cares" << std::endl;
    std::cout << "in: output program inputs with non-det values for don cares" << std::endl;
    std::cout << "it: output program inputs for last trace" << std::endl;
    std::cout << "i file: output program inputs for [json] file trace" << std::endl;
    std::cout << "j: output json trace" << std::endl;
    std::cout << "o: output goto trace" << std::endl;
    std::cout << "q: quit" << std::endl;
    std::cout << "r: run until completion" << std::endl;
    std::cout << "s#: step a number of instructions" << std::endl;
    std::cout << "sa: step across a function" << std::endl;
    std::cout << "so: step out of a function" << std::endl;
  } else if(ch=='i') {
    ch=tolower(command[1]);
    if(ch=='d')     list_inputs(false);
    else if(ch=='n') list_inputs(true);
    else if(ch=='t') load_counter_example_inputs(steps);
    else if(ch==' ') load_counter_example_inputs(command+3);
    num_steps=0;
    print_inputs();
  } else if(ch=='j') {
    num_steps=0;
    jsont json_steps;
    convert(ns, steps, json_steps);
    ch=tolower(command[1]);
    if(ch==' ') {
      std::ofstream file;
      file.open(command+2);
      if(file.is_open()) {
        json_steps.output(file);
        file.close();
        return;
      }
    }
    json_steps.output(std::cout);
  } else if(ch=='o') {
    num_steps=0;
    ch=tolower(command[1]);
    if(ch==' ') {
      std::ofstream file;
      file.open(command+2);
      if(file.is_open()) {
        steps.output(ns, file);
        file.close();
        return;
      }
    }
    steps.output(ns, std::cout);
  } else if(ch=='r') {
    num_steps=-1;
  } else if(ch=='s') {
    ch=tolower(command[1]);
    if(ch=='e')
      num_steps=-1;
    if(ch=='o')
      stack_depth=call_stack.size();
    if(ch=='a')
      stack_depth=call_stack.size()+1;
    else {
      num_steps=atoi(command+1);
      if(num_steps==0)
        num_steps=1;
    }
  }
}

/*******************************************************************\

Function: interpretert::step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::step()
{
  if(PC==function->second.body.instructions.end())
  {
    if(call_stack.empty())
      done=true;
    else
    {
      PC=call_stack.top().return_PC;
      function=call_stack.top().return_function;
      stack_pointer=call_stack.top().old_stack_pointer;
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
    /*trace_step.full_lhs=step.full_lhs;
    trace_step.lhs_object=to_symbol_expr(trace_step.full_lhs);
    trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);*/
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
  default:
    throw "encountered instruction with undefined instruction type";
  }
  
  PC=next_PC;
}

/*******************************************************************\

Function: interpretert::execute_goto

  Inputs:

 Outputs:

 Purpose:

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

 Purpose:

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

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
irep_idt interpretert::get_component_id(irep_idt &object,unsigned offset)
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

Function: interpretert::get_value

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
exprt interpretert::get_value(const typet &type, unsigned offset)
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
    exprt result(ID_constant, type);
    //array_exprt result(type);
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
  if(memory[offset].initialised>=0)
    return side_effect_expr_nondett(type);
  std::vector<mp_integer> rhs;
  rhs.push_back(memory[offset].value);
  return get_value(type, rhs);
}

/*******************************************************************
 Function: interpretert::get_value

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
exprt interpretert::get_value(const typet &type, std::vector<mp_integer> &rhs,unsigned offset)
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
    //array_exprt result(type);
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
  } else if(real_type.id()==ID_fixedbv) {
    fixedbvt f;
    f.from_integer(rhs[offset]);
    return f.to_expr();
  } else if(real_type.id()==ID_bool) {
    if(rhs[offset]!=0)
      return true_exprt();
    else
      return false_exprt();
  } else if((real_type.id()==ID_pointer) || (real_type.id()==ID_address_of)) {
      if(rhs[offset]==0)
      {
        constant_exprt result(type);
        result.set_value(ID_NULL);
        return result;
      }
      if(rhs[offset]<memory.size()) {
        memory_cellt &cell=memory[integer2unsigned(rhs[offset])];
        const symbolt &symbol=ns.lookup(cell.identifier);
        exprt symbol_expr(ID_symbol, symbol.type);
        symbol_expr.set(ID_identifier, cell.identifier);
        if(cell.offset==0) return address_of_exprt(symbol_expr);

        if(ns.follow(symbol.type).id()==ID_struct) {
          irep_idt member_id=get_component_id(cell.identifier,cell.offset);
          member_exprt member_expr(symbol_expr,member_id);
          return address_of_exprt(member_expr);
        }
        index_exprt index_expr(symbol_expr,from_integer(cell.offset, integer_typet()));
        return index_expr;
      }
      throw "pointer out of memory";
  }
  return from_integer(rhs[offset], type);
}

/*******************************************************************

Function: interpretert::execute_assign

  Inputs:

 Outputs:

 Purpose:

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
      std::cout << "!! failed to obtain rhs ("
                << rhs.size() << " vs. "
                << size << ")" << std::endl;
    else
    {
      goto_trace_stept &trace_step=steps.get_last_step();
      assign(address, rhs);
      trace_step.full_lhs=code_assign.lhs();
      trace_step.lhs_object=ssa_exprt(trace_step.full_lhs);
      trace_step.full_lhs_value=get_value(trace_step.full_lhs.type(),rhs);
      trace_step.lhs_object_value=trace_step.full_lhs_value;
    }
  }
}

/*******************************************************************\

Function: interpretert::assign

  Inputs:

 Outputs:

 Purpose:

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
        std::cout << "** assigning " << cell.identifier << "["
            << cell.offset << "]:=" << rhs[i] << std::endl;
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
    throw "assertion failed";
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
  const memory_cellt &cell=memory[integer2long(a)];
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
      unsigned size=get_size(symbol.type);
      
      if(size!=0)
      {
        frame.local_map[id]=stack_pointer;

        for(unsigned i=0;i<stack_pointer;i++)
        {
          unsigned address=stack_pointer+i;
          if(address>=memory.size()) memory.resize(address+1);
          memory[address].value=0;
          memory[address].identifier=id;
          memory[address].offset=i;
          memory[address].initialised=0;
        }
        
        stack_pointer+=size;
      }
    }
        
    // assign the arguments
    const code_typet::parameterst &parameters=
      to_code_type(f_it->second.type).parameters();

    if(argument_values.size()<parameters.size())
      throw "not enough arguments";

    for(unsigned i=0;i<parameters.size();i++)
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
    std::cout << "no body for "+id2string(identifier);//TODO:used to be throw. need some better approach? need to check state of buffers (and by refs)
}

/*******************************************************************\

Function: interpretert::build_memory_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::build_memory_map()
{
  // put in a dummy for NULL
  memory.resize(1);
  memory[0].offset=0;
  memory[0].identifier="NULL-OBJECT";
  memory[0].initialised=0;

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

    mp_integer i;
    if(!to_integer(size_expr, i))
      return subtype_size*integer2unsigned(i);
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

Function: fill_inputs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void interpretert::fill_inputs(input_varst &inputs) {
  for(input_varst::iterator it=inputs.begin();it!=inputs.end();it++) {
    std::vector<mp_integer> rhs;
    evaluate(it->second, rhs);
    if(rhs.empty())
      continue;
    memory_mapt::const_iterator m_it1=memory_map.find(it->first);
    if(m_it1==memory_map.end())
      continue;
    mp_integer address=m_it1->second;
    unsigned size=get_size(it->second.type());
    if(size!=rhs.size())
      continue;
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
      symbolt symbol=symbol_table.lookup(cell.identifier);
      if(use_non_det) {
        exprt value=get_value(symbol.type, i - cell.offset);
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
        exprt value=get_value(symbol.type, rhs);
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
    if(cell.offset>0)
      continue;
    if((cell.initialised<0)
        && (strncmp(cell.identifier.c_str(), "__CPROVER", 9)!=0)) {
      input_vars[cell.identifier]=inputs[cell.identifier];
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
    std::cout << it->first << "=" << from_expr(ns, it->first, it->second)
        << std::endl;
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
  message_clientt messgae_client;
  if(parse_json(filename, messgae_client.get_message_handler(),
      counter_example)) {
    show=false;
    input_varst inputs;
    for(jsont::objectt::const_iterator it=counter_example.object.end();
        it!=counter_example.object.begin();) {
      it--;
      irep_idt id=it->second["lhs"].value;
      inputs[id]=to_expr(ns, id, it->second["value"].value);
    }
    try {
      initialise(true);
      fill_inputs(inputs);
      while(!done)
        step();
    } catch(const char *e) {
      std::cout << e << std::endl;
    }
    list_inputs(inputs);
    show=true;
  }
  return input_vars;
}

interpretert::input_varst& interpretert::load_counter_example_inputs(goto_tracet &trace) {
  jsont counter_example;
  message_clientt messgae_client;
  show=false;
  input_varst inputs;
  for(goto_tracet::stepst::iterator it=trace.steps.end();it!=trace.steps.begin();)
  {
    it--;
    if(it->pc->is_other() || it->pc->is_assign())
    {
      irep_idt id=to_symbol_expr(it->full_lhs).get_identifier();
      inputs[id]=it->full_lhs_value;
    }
  }
  try {
    initialise(true);
    fill_inputs(inputs);
    while(!done) {
      show_state();
      step();
    }
  } catch(const char *e) {
    std::cout << e << std::endl;
  }
  list_inputs(inputs);
  show=true;
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
  const goto_functionst &goto_functions)
{
  interpretert interpreter(symbol_table, goto_functions);
  interpreter();
}
