/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <cstdio>
#include <iostream>
#include <algorithm>

#include <util/std_types.h>
#include <util/symbol_table.h>
#include <util/ieee_float.h>
#include <util/fixedbv.h>
#include <util/std_expr.h>
#include <ansi-c/c_types.h>

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
  
  try {
	std::cout << "Type h for help";
    while(!done)
    {
      num_steps=1;
      stack_depth=-1;
      show_state();
      command();
      while (!done && ((num_steps<0) || ((num_steps--)>0))) {
        step();
        show_state();
      }
      while (!done && (stack_depth<=call_stack.size()) && (stack_depth>=0)) {
        step();
        show_state();
      }
    }
    std::cout << "Program End." << std::endl;
  }
  catch(const char *e)
  {
    std::cout << e << std::endl;
  }
  while(!done) {
    command();
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
  std::cout << std::endl;
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
  else if (ch=='h') {
    num_steps=0;
    std::cout << "Interpreter help" << std::endl;
    std::cout << "h: display this menu" << std::endl;
    std::cout << "j: output json trace" << std::endl;
    std::cout << "o: output goto trace" << std::endl;
    std::cout << "q: quit" << std::endl;
    std::cout << "r: run until completion" << std::endl;
    std::cout << "s#: step a number of instructions" << std::endl;
    std::cout << "sa: step across a function" << std::endl;
    std::cout << "so: step out of a function" << std::endl;
  }
  else if (ch=='j') {
    num_steps=0;
    jsont json_steps;
    convert(ns,steps,json_steps);
    json_steps.output(std::cout);
  }
  else if (ch=='o') {
    num_steps=0;
    steps.output(ns,std::cout);
  }
  else if (ch=='r') {
    num_steps=-1;
  }
  else if (ch=='s') {
    ch=tolower(command[1]);
    if (ch=='o')
      stack_depth=call_stack.size();
    if (ch=='a')
      stack_depth=call_stack.size()+1;
    else {
      num_steps=atoi(command+1);
      if (num_steps==0) num_steps=1;
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

/*******************************************************************\

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
    else {
      goto_trace_stept &trace_step=steps.get_last_step();
      assign(address, rhs);
      trace_step.full_lhs=code_assign.lhs();
      trace_step.lhs_object=ssa_exprt(trace_step.full_lhs);
      if(trace_step.full_lhs.type().id()==ID_struct)
      {
      }
      else if(trace_step.full_lhs.type().id()==ID_floatbv)
      {
        ieee_floatt f;
        f.spec=to_floatbv_type(trace_step.full_lhs.type());
        f.unpack(rhs[0]);
        lhs_at_pc=f.to_expr();
      }
      else if(trace_step.full_lhs.type().id()==ID_fixedbv)
      {
        fixedbvt f;
        f.from_integer(rhs[0]);
        lhs_at_pc=f.to_expr();
      }
      else if(trace_step.full_lhs.type().id()==ID_bool)
      {
        if (trace_step.full_lhs.is_true()) 
          lhs_at_pc=true_exprt();
        else 
          lhs_at_pc=false_exprt();
      }
      else
      {
          lhs_at_pc=from_integer(rhs[0],size_type());
      }
      trace_step.full_lhs_value=lhs_at_pc;
      trace_step.lhs_object_value = lhs_at_pc;
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
  for(unsigned i=0; i<rhs.size(); i++, ++address)
  {
    if(address<memory.size())
    {
      memory_cellt &cell=memory[integer2unsigned(address)];
      std::cout << "** assigning " << cell.identifier
                << "[" << cell.offset << "]:=" << rhs[i] << std::endl;
      cell.value=rhs[i];
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
  std::vector<std::vector<mp_integer> > argument_values;
  
  argument_values.resize(function_call.arguments().size());
  
  for(std::size_t i=0; i<function_call.arguments().size(); i++)
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

        for(unsigned i=0; i<stack_pointer; i++)
        {
          unsigned address=stack_pointer+i;
          if(address>=memory.size()) memory.resize(address+1);
          memory[address].value=0;
          memory[address].identifier=id;
          memory[address].offset=i;
        }
        
        stack_pointer+=size;
      }
    }
        
    // assign the arguments
    const code_typet::parameterst &parameters=
      to_code_type(f_it->second.type).parameters();

    if(argument_values.size()<parameters.size())
      throw "not enough arguments";

    for(unsigned i=0; i<parameters.size(); i++)
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
    throw "no body for "+id2string(identifier);
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
    
    for(unsigned i=0; i<size; i++)
    {
      memory_cellt &cell=memory[address+i];
      cell.identifier=symbol.name;
      cell.offset=i;
      cell.value=0;
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
  else
    return 1;
}

/*******************************************************************\

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
