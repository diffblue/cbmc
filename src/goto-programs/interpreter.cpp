/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <cstdio>
#include <iostream>

#include <std_types.h>
#include <symbol_table.h>

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
    main_it=goto_functions.function_map.find(ID_main);

  if(main_it==goto_functions.function_map.end())
    throw "main not found";
  
  const goto_functionst::goto_functiont &goto_function=main_it->second;
  
  if(!goto_function.body_available)
    throw "main has no body";

  PC=goto_function.body.instructions.begin();
  function=main_it;
    
  done=false;
  
  while(!done)
  {
    show_state();
    command();
    if(!done) step();
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

  switch(PC->type)
  {
  case GOTO:
    execute_goto();
    break;
  
  case ASSUME:
    execute_assume();
    break;
  
  case ASSERT:
    execute_assert();
    break;
  
  case OTHER:
    execute_other();
    break;
  
  case DECL:
    execute_decl();
    break;
  
  case SKIP:
  case LOCATION:
  case END_FUNCTION:
    break;
  
  case RETURN:
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
    execute_assign();
    break;
    
  case FUNCTION_CALL:
    execute_function_call();
    break;
  
  case START_THREAD:
    throw "START_THREAD not yet implemented";
  
  case END_THREAD:
    throw "END_THREAD not yet implemented";
    break;

  case ATOMIC_BEGIN:
    throw "ATOMIC_BEGIN not yet implemented";
    
  case ATOMIC_END:
    throw "ATOMIC_END not yet implemented";
    
  case DEAD:
    throw "DEAD not yet implemented";
  
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
    if(PC->targets.size()==0)
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
  
  if(rhs.size()!=0)
  {
    mp_integer address=evaluate_address(code_assign.lhs());  
    unsigned size=get_size(code_assign.lhs().type());

    if(size!=rhs.size())
      std::cout << "!! failed to obtain rhs ("
                << rhs.size() << " vs. "
                << size << ")" << std::endl;
    else
      assign(address, rhs);
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
      memory_cellt &cell=memory[integer2long(address)];
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

  const memory_cellt &cell=memory[integer2long(a)];
  const irep_idt &identifier=cell.identifier;

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
  
  for(unsigned i=0; i<function_call.arguments().size(); i++)
    evaluate(function_call.arguments()[i], argument_values[i]);

  // do the call
      
  if(f_it->second.body_available)
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
    const code_typet::argumentst &arguments=
      to_code_type(f_it->second.type).arguments();

    if(argument_values.size()<arguments.size())
      throw "not enough arguments";

    for(unsigned i=0; i<arguments.size(); i++)
    {
      const code_typet::argumentt &a=arguments[i];
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
    const irept::subt &components=
      type.find(ID_components).get_sub();

    unsigned sum=0;

    forall_irep(it, components)
    {
      const typet &sub_type=static_cast<const typet &>(it->find(ID_type));

      if(sub_type.id()!=ID_code)
        sum+=get_size(sub_type);
    }
    
    return sum;
  }
  else if(type.id()==ID_union)
  {
    const irept::subt &components=
      type.find(ID_components).get_sub();

    unsigned max_size=0;

    forall_irep(it, components)
    {
      const typet &sub_type=static_cast<const typet &>(it->find(ID_type));

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
      return subtype_size*integer2long(i);
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
