/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#include "interpreter.h"

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
#include <json/json_parser.h>

#include "interpreter_class.h"
#include "remove_returns.h"

const size_t interpretert::npos=std::numeric_limits<size_t>::max();

void interpretert::operator()()
{
  status() << "0- Initialize:" << eom;
  initialize(true);
  try
  {
    status() << "Type h for help\n" << eom;

    while(!done)
      command();

    status() << total_steps << "- Program End.\n" << eom;
  }
  catch (const char *e)
  {
    error() << e << "\n" << eom;
  }

  while(!done)
    command();
}

/// Initializes the memory map of the interpreter and [optionally] runs up to
/// the entry point (thus doing the cprover initialization)
void interpretert::initialize(bool init)
{
  build_memory_map();

  total_steps=0;
  const goto_functionst::function_mapt::const_iterator
    main_it=goto_functions.function_map.find(goto_functionst::entry_point());

  if(main_it==goto_functions.function_map.end())
    throw "main not found";

  const goto_functionst::goto_functiont &goto_function=main_it->second;

  if(!goto_function.body_available())
    throw "main has no body";

  pc=goto_function.body.instructions.begin();
  function=main_it;

  done=false;
  if(init)
  {
    stack_depth=call_stack.size()+1;
    show_state();
    step();
    while(!done && (stack_depth<=call_stack.size()) && (stack_depth!=npos))
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

/// displays the current position of the pc and corresponding code
void interpretert::show_state()
{
  if(!show)
    return;
  status() << "\n"
           << total_steps+1
           << " ----------------------------------------------------\n";

  if(pc==function->second.body.instructions.end())
  {
    status() << "End of function `" << function->first << "'\n";
  }
  else
    function->second.body.output_instruction(
      ns,
      function->first,
      status(),
      pc);

  status() << eom;
}

/// reads a user command and executes it.
void interpretert::command()
{
  #define BUFSIZE 100
  char command[BUFSIZE];
  if(fgets(command, BUFSIZE-1, stdin)==nullptr)
  {
    done=true;
    return;
  }

  char ch=tolower(command[0]);
  if(ch=='q')
    done=true;
  else if(ch=='h')
  {
    status()
      << "Interpreter help\n"
      << "h: display this menu\n"
      << "j: output json trace\n"
      << "m: output memory dump\n"
      << "o: output goto trace\n"
      << "q: quit\n"
      << "r: run until completion\n"
      << "s#: step a number of instructions\n"
      << "sa: step across a function\n"
      << "so: step out of a function\n"
      << eom;
  }
  else if(ch=='j')
  {
    jsont json_steps;
    convert(ns, steps, json_steps);
    ch=tolower(command[1]);
    if(ch==' ')
    {
      std::ofstream file;
      file.open(command+2);
      if(file.is_open())
      {
        json_steps.output(file);
        file.close();
        return;
      }
    }
    json_steps.output(result());
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
    steps.output(ns, result());
  }
  else if(ch=='r')
  {
    ch=tolower(command[1]);
    initialize(ch!='0');
  }
  else if((ch=='s') || (ch==0))
  {
    num_steps=1;
    stack_depth=npos;
    ch=tolower(command[1]);
    if(ch=='e')
      num_steps=npos;
    else if(ch=='o')
      stack_depth=call_stack.size();
    else if(ch=='a')
      stack_depth=call_stack.size()+1;
    else
    {
      num_steps=atoi(command+1);
      if(num_steps==0)
        num_steps=1;
    }
    while(!done && ((num_steps==npos) || ((num_steps--)>0)))
    {
      step();
      show_state();
    }
    while(!done && (stack_depth<=call_stack.size()) && (stack_depth!=npos))
    {
      step();
      show_state();
    }
    return;
  }
  show_state();
}

/// executes a single step and updates the program counter
void interpretert::step()
{
  total_steps++;
  if(pc==function->second.body.instructions.end())
  {
    if(call_stack.empty())
      done=true;
    else
    {
      pc=call_stack.top().return_pc;
      function=call_stack.top().return_function;
      // TODO: this increases memory size quite quickly.
      // Should check alternatives
      call_stack.pop();
    }

    return;
  }

  next_pc=pc;
  next_pc++;

  steps.add_step(goto_trace_stept());
  goto_trace_stept &trace_step=steps.get_last_step();
  trace_step.thread_nr=thread_id;
  trace_step.pc=pc;
  switch(pc->type)
  {
  case GOTO:
    trace_step.type=goto_trace_stept::typet::GOTO;
    execute_goto();
    break;

  case ASSUME:
    trace_step.type=goto_trace_stept::typet::ASSUME;
    execute_assume();
    break;

  case ASSERT:
    trace_step.type=goto_trace_stept::typet::ASSERT;
    execute_assert();
    break;

  case OTHER:
    execute_other();
    break;

  case DECL:
    trace_step.type=goto_trace_stept::typet::DECL;
    execute_decl();
    break;

  case SKIP:
  case LOCATION:
    trace_step.type=goto_trace_stept::typet::LOCATION;
    break;
  case END_FUNCTION:
    trace_step.type=goto_trace_stept::typet::FUNCTION_RETURN;
    break;

  case RETURN:
    trace_step.type=goto_trace_stept::typet::FUNCTION_RETURN;
    if(call_stack.empty())
      throw "RETURN without call"; // NOLINT(readability/throw)

    if(pc->code.operands().size()==1 &&
       call_stack.top().return_value_address!=0)
    {
      mp_vectort rhs;
      evaluate(pc->code.op0(), rhs);
      assign(call_stack.top().return_value_address, rhs);
    }

    next_pc=function->second.body.instructions.end();
    break;

  case ASSIGN:
    trace_step.type=goto_trace_stept::typet::ASSIGNMENT;
    execute_assign();
    break;

  case FUNCTION_CALL:
    trace_step.type=goto_trace_stept::typet::FUNCTION_CALL;
    execute_function_call();
    break;

  case START_THREAD:
    trace_step.type=goto_trace_stept::typet::SPAWN;
    throw "START_THREAD not yet implemented"; // NOLINT(readability/throw)

  case END_THREAD:
    throw "END_THREAD not yet implemented"; // NOLINT(readability/throw)
    break;

  case ATOMIC_BEGIN:
    trace_step.type=goto_trace_stept::typet::ATOMIC_BEGIN;
    throw "ATOMIC_BEGIN not yet implemented"; // NOLINT(readability/throw)

  case ATOMIC_END:
    trace_step.type=goto_trace_stept::typet::ATOMIC_END;
    throw "ATOMIC_END not yet implemented"; // NOLINT(readability/throw)

  case DEAD:
    trace_step.type=goto_trace_stept::typet::DEAD;
    break;
  case THROW:
    trace_step.type=goto_trace_stept::typet::GOTO;
    while(!done && (pc->type!=CATCH))
    {
      if(pc==function->second.body.instructions.end())
      {
        if(call_stack.empty())
          done=true;
        else
        {
          pc=call_stack.top().return_pc;
          function=call_stack.top().return_function;
          call_stack.pop();
        }
      }
      else
      {
        next_pc=pc;
        next_pc++;
      }
    }
    break;
  case CATCH:
    break;
  default:
    throw "encountered instruction with undefined instruction type";
  }
  pc=next_pc;
}

/// executes a goto instruction
void interpretert::execute_goto()
{
  if(evaluate_boolean(pc->guard))
  {
    if(pc->targets.empty())
      throw "taken goto without target";

    if(pc->targets.size()>=2)
      throw "non-deterministic goto encountered";

    next_pc=pc->targets.front();
  }
}

/// executes side effects of 'other' instructions
void interpretert::execute_other()
{
  const irep_idt &statement=pc->code.get_statement();
  if(statement==ID_expression)
  {
    assert(pc->code.operands().size()==1);
    mp_vectort rhs;
    evaluate(pc->code.op0(), rhs);
  }
  else if(statement==ID_array_set)
  {
    mp_vectort tmp, rhs;
    evaluate(pc->code.op1(), tmp);
    mp_integer address=evaluate_address(pc->code.op0());
    size_t size=get_size(pc->code.op0().type());
    while(rhs.size()<size) rhs.insert(rhs.end(), tmp.begin(), tmp.end());
    if(size!=rhs.size())
      error() << "!! failed to obtain rhs (" << rhs.size() << " vs. "
              << size << ")\n" << eom;
    else
    {
      assign(address, rhs);
    }
  }
  else if(statement==ID_output)
  {
    return;
  }
  else
    throw "unexpected OTHER statement: "+id2string(statement);
}

void interpretert::execute_decl()
{
  assert(pc->code.get_statement()==ID_decl);
}

/// retrieves the member at offset
/// \par parameters: an object and a memory offset
irep_idt interpretert::get_component_id(
  const irep_idt &object,
  unsigned offset)
{
  const symbolt &symbol=ns.lookup(object);
  const typet real_type=ns.follow(symbol.type);
  if(real_type.id()!=ID_struct)
    throw "request for member of non-struct";

  const struct_typet &struct_type=to_struct_type(real_type);
  const struct_typet::componentst &components=struct_type.components();
  for(struct_typet::componentst::const_iterator it=components.begin();
      it!=components.end(); it++)
  {
    if(offset<=0)
      return it->id();
    size_t size=get_size(it->type());
    offset-=size;
  }
  return object;
}

/// returns the type object corresponding to id
typet interpretert::get_type(const irep_idt &id) const
{
  dynamic_typest::const_iterator it=dynamic_types.find(id);
  if(it==dynamic_types.end())
    return symbol_table.lookup(id).type;
  return it->second;
}

/// retrives the constant value at memory location offset as an object of type
/// type
exprt interpretert::get_value(
  const typet &type,
  std::size_t offset,
  bool use_non_det)
{
  const typet real_type=ns.follow(type);
  if(real_type.id()==ID_struct)
  {
    exprt result=struct_exprt(real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();

    // Retrieve the values for the individual members
    result.reserve_operands(components.size());
    for(struct_typet::componentst::const_iterator it=components.begin();
        it!=components.end(); it++)
    {
      size_t size=get_size(it->type());
      const exprt operand=get_value(it->type(), offset);
      offset+=size;
      result.copy_to_operands(operand);
    }
    return result;
  }
  else if(real_type.id()==ID_array)
  {
    // Get size of array
    exprt result=array_exprt(to_array_type(real_type));
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));
    size_t subtype_size=get_size(type.subtype());
    mp_integer mp_count;
    to_integer(size_expr, mp_count);
    unsigned count=integer2unsigned(mp_count);

    // Retrieve the value for each member in the array
    result.reserve_operands(count);
    for(unsigned i=0; i<count; i++)
    {
      const exprt operand=get_value(type.subtype(),
          offset+i*subtype_size);
      result.copy_to_operands(operand);
    }
    return result;
  }
  if(use_non_det && (memory[offset].initialized>=0))
    return side_effect_expr_nondett(type);
  mp_vectort rhs;
  rhs.push_back(memory[offset].value);
  return get_value(type, rhs);
}

/// returns the value at offset in the form of type given a memory buffer rhs
/// which is typically a structured type
exprt interpretert::get_value(
  const typet &type,
  mp_vectort &rhs,
  std::size_t offset)
{
  const typet real_type=ns.follow(type);
  assert(!rhs.empty());

  if(real_type.id()==ID_struct)
  {
    exprt result=struct_exprt(real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();

    // Retrieve the values for the individual members
    result.reserve_operands(components.size());
    for(const struct_union_typet::componentt &expr : components)
    {
      size_t size=get_size(expr.type());
      const exprt operand=get_value(expr.type(), rhs, offset);
      offset+=size;
      result.copy_to_operands(operand);
    }
    return result;
  }
  else if(real_type.id()==ID_array)
  {
    exprt result(ID_constant, type);
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));

    // Get size of array
    size_t subtype_size=get_size(type.subtype());
    mp_integer mp_count;
    to_integer(size_expr, mp_count);
    unsigned count=integer2unsigned(mp_count);

    // Retrieve the value for each member in the array
    result.reserve_operands(count);
    for(unsigned i=0; i<count; i++)
    {
      const exprt operand=get_value(type.subtype(), rhs,
          offset+i*subtype_size);
      result.copy_to_operands(operand);
    }
    return result;
  }
  else if(real_type.id()==ID_floatbv)
  {
    ieee_floatt f(to_floatbv_type(type));
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
      false_exprt();
  }
  else if(real_type.id()==ID_c_bool)
  {
    return from_integer(rhs[offset]!=0?1:0, type);
  }
  else if((real_type.id()==ID_pointer) || (real_type.id()==ID_address_of))
  {
    if(rhs[offset]==0)
    {
      // NULL pointer
      constant_exprt result(type);
      result.set_value(ID_NULL);
      return result;
    }
    if(rhs[offset]<memory.size())
    {
      // We want the symbol pointed to
      std::size_t address=integer2size_t(rhs[offset]);
      irep_idt identifier=address_to_identifier(address);
      size_t offset=address_to_offset(address);
      const typet type=get_type(identifier);
      exprt symbol_expr(ID_symbol, type);
      symbol_expr.set(ID_identifier, identifier);

      if(offset==0)
        return address_of_exprt(symbol_expr);
      if(ns.follow(type).id()==ID_struct)
      {
        irep_idt member_id=get_component_id(identifier, offset);
        member_exprt member_expr(symbol_expr, member_id);
        return address_of_exprt(member_expr);
      }
      index_exprt index_expr(
        symbol_expr,
        from_integer(offset, integer_typet()));
      return index_expr;
    }

    error() << "interpreter: invalid pointer " << rhs[offset]
            << " > object count " << memory.size() << eom;
    throw "interpreter: reading from invalid pointer";
  }
  else if(real_type.id()==ID_string)
  {
    // Strings are currently encoded by their irep_idt ID.
    return constant_exprt(
      irep_idt::make_from_table_index(rhs[offset].to_long()),
      type);
  }
  // Retrieve value of basic data type
  return from_integer(rhs[offset], type);
}

/// executes the assign statement at the current pc value
void interpretert::execute_assign()
{
  const code_assignt &code_assign=
    to_code_assign(pc->code);

  mp_vectort rhs;
  evaluate(code_assign.rhs(), rhs);

  if(!rhs.empty())
  {
    mp_integer address=evaluate_address(code_assign.lhs());
    size_t size=get_size(code_assign.lhs().type());

    if(size!=rhs.size())
      error() << "!! failed to obtain rhs ("
              << rhs.size() << " vs. "
              << size << ")\n"
              << eom;
    else
    {
      goto_trace_stept &trace_step=steps.get_last_step();
      assign(address, rhs);
      trace_step.full_lhs=code_assign.lhs();

      // TODO: need to look at other cases on ssa_exprt
      // (dereference should be handled on ssa)
      if(ssa_exprt::can_build_identifier(trace_step.full_lhs))
      {
        trace_step.lhs_object=ssa_exprt(trace_step.full_lhs);
      }
      trace_step.full_lhs_value=get_value(trace_step.full_lhs.type(), rhs);
      trace_step.lhs_object_value=trace_step.full_lhs_value;
    }
  }
  else if(code_assign.rhs().id()==ID_side_effect)
  {
    side_effect_exprt side_effect=to_side_effect_expr(code_assign.rhs());
    if(side_effect.get_statement()==ID_nondet)
    {
      unsigned address=integer2unsigned(evaluate_address(code_assign.lhs()));
      size_t size=get_size(code_assign.lhs().type());
      for(size_t i=0; i<size; i++)
      {
        memory[address+i].initialized=-1;
      }
    }
  }
}

/// sets the memory at address with the given rhs value (up to sizeof(rhs))
void interpretert::assign(
  mp_integer address,
  const mp_vectort &rhs)
{
  for(size_t i=0; i<rhs.size(); i++)
  {
    if((address+i)<memory.size())
    {
      std::size_t address_val=integer2size_t(address+i);
      memory_cellt &cell=memory[address_val];
      if(show)
      {
        status() << total_steps << " ** assigning "
                 << address_to_identifier(address_val) << "["
                 << address_to_offset(address_val) << "]:=" << rhs[i]
                 << "\n" << eom;
      }
      cell.value=rhs[i];
      if(cell.initialized==0)
        cell.initialized=1;
    }
  }
}

void interpretert::execute_assume()
{
  if(!evaluate_boolean(pc->guard))
    throw "assumption failed";
}

void interpretert::execute_assert()
{
  if(!evaluate_boolean(pc->guard))
  {
    if((target_assert==pc) || stop_on_assertion)
      throw "program assertion reached";
    else if(show)
      error() << "assertion failed at " << pc->location_number
              << "\n" << eom;
  }
}

void interpretert::execute_function_call()
{
  const code_function_callt &function_call=
    to_code_function_call(pc->code);

  // function to be called
  mp_integer a=evaluate_address(function_call.function());

  if(a==0)
    throw "function call to NULL";
  else if(a>=memory.size())
    throw "out-of-range function call";

  // Retrieve the empty last trace step struct we pushed for this step
  // of the interpreter run to fill it with the corresponding data
  goto_trace_stept &trace_step=steps.get_last_step();
  std::size_t address=integer2size_t(a);
  const memory_cellt &cell=memory[address];
  const irep_idt &identifier=address_to_identifier(address);
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
  std::vector<mp_vectort> argument_values;

  argument_values.resize(function_call.arguments().size());

  for(std::size_t i=0; i<function_call.arguments().size(); i++)
    evaluate(function_call.arguments()[i], argument_values[i]);

  // do the call

  if(f_it->second.body_available())
  {
    call_stack.push(stack_framet());
    stack_framet &frame=call_stack.top();

    frame.return_pc=next_pc;
    frame.return_function=function;
    frame.old_stack_pointer=stack_pointer;
    frame.return_value_address=return_value_address;

    // local variables
    std::set<irep_idt> locals;
    get_local_identifiers(f_it->second, locals);

    for(const auto &id : locals)
    {
      const symbolt &symbol=ns.lookup(id);
      frame.local_map[id]=integer2unsigned(build_memory_map(id, symbol.type));
    }

    // assign the arguments
    const code_typet::parameterst &parameters=
      to_code_type(f_it->second.type).parameters();

    if(argument_values.size()<parameters.size())
      throw "not enough arguments";

    for(size_t i=0; i<parameters.size(); i++)
    {
      const code_typet::parametert &a=parameters[i];
      exprt symbol_expr(ID_symbol, a.type());
      symbol_expr.set(ID_identifier, a.get_identifier());
      assert(i<argument_values.size());
      assign(evaluate_address(symbol_expr), argument_values[i]);
    }

    // set up new pc
    function=f_it;
    next_pc=f_it->second.body.instructions.begin();
  }
  else
  {
    list_input_varst::iterator it=
        function_input_vars.find(function_call.function().get(ID_identifier));
    if(it!=function_input_vars.end())
    {
      mp_vectort value;
      assert(!it->second.empty());
      assert(!it->second.front().return_assignments.empty());
      evaluate(it->second.front().return_assignments.back().value, value);
      if(return_value_address>0)
      {
        assign(return_value_address, value);
      }
      it->second.pop_front();
      return;
    }
    if(show)
      error() << "no body for "+id2string(identifier) << eom;
  }
}

/// Creates a memory map of all static symbols in the program
void interpretert::build_memory_map()
{
  // put in a dummy for NULL
  memory.resize(1);
  inverse_memory_map[0]="NULL-OBJECT";

  num_dynamic_objects=0;
  dynamic_types.clear();

  // now do regular static symbols
  for(const auto &s : symbol_table.symbols)
    build_memory_map(s.second);

  // for the locals
  stack_pointer=memory.size();
}

void interpretert::build_memory_map(const symbolt &symbol)
{
  size_t size=0;

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
    std::size_t address=memory.size();
    memory.resize(address+size);
    memory_map[symbol.name]=address;
    inverse_memory_map[address]=symbol.name;
  }
}

/// turns a variable length array type into a fixed array type
typet interpretert::concretize_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));
    mp_vectort computed_size;
    evaluate(size_expr, computed_size);
    if(computed_size.size()==1 &&
       computed_size[0]>=0)
    {
      result() << "Concretized array with size " << computed_size[0]
               << eom;
      return array_typet(type.subtype(),
             constant_exprt::integer_constant(computed_size[0].to_ulong()));
    }
    else
    {
      error() << "Failed to concretize variable array"
              << eom;
    }
  }
  return type;
}

/// Populates dynamic entries of the memory map
/// \return Updates the memory map to include variable id if it does not exist
mp_integer interpretert::build_memory_map(
  const irep_idt &id,
  const typet &type)
{
  typet alloc_type=concretize_type(type);
  size_t size=get_size(alloc_type);
  auto it=dynamic_types.find(id);

  if(it!=dynamic_types.end())
  {
    std::size_t address=memory_map[id];
    std::size_t current_size=base_address_to_alloc_size(address);
    // current size <= size already recorded
    if(size<=current_size)
      return memory_map[id];
  }

  // The current size is bigger then the one previously recorded
  // in the memory map

  if(size==0)
    size=1; // This is a hack to create existence

  std::size_t address=memory.size();
  memory.resize(address+size);
  memory_map[id]=address;
  inverse_memory_map[address]=id;
  dynamic_types.insert(std::pair<const irep_idt, typet>(id, alloc_type));

  return address;
}

/// Retrieves the actual size of the provided structured type. Unbounded objects
/// get allocated 2^32 address space each (of a 2^64 sized space).
/// \param type: a structured type
/// \return Size of the given type
size_t interpretert::get_size(const typet &type)
{
  if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    unsigned sum=0;

    for(const auto &comp : components)
    {
      const typet &sub_type=comp.type();

      if(sub_type.id()!=ID_code)
        sum+=get_size(sub_type);
    }

    return sum;
  }
  else if(type.id()==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    size_t max_size=0;

    for(const auto &comp : components)
    {
      const typet &sub_type=comp.type();

      if(sub_type.id()!=ID_code)
        max_size=std::max(max_size, get_size(sub_type));
    }

    return max_size;
  }
  else if(type.id()==ID_array)
  {
    const exprt &size_expr=static_cast<const exprt &>(type.find(ID_size));

    size_t subtype_size=get_size(type.subtype());

    mp_vectort i;
    evaluate(size_expr, i);
    if(i.size()==1)
    {
      // Go via the binary representation to reproduce any
      // overflow behaviour.
      exprt size_const=from_integer(i[0], size_expr.type());
      mp_integer size_mp;
      assert(!to_integer(size_const, size_mp));
      return subtype_size*integer2unsigned(size_mp);
    }
    return subtype_size;
  }
  else if(type.id()==ID_symbol)
  {
    return get_size(ns.follow(type));
  }
  return 1;
}

exprt interpretert::get_value(const irep_idt &id)
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

  symbol_exprt symbol_expr(id, get_type);
  mp_integer whole_lhs_object_address=evaluate_address(symbol_expr);

  return get_value(get_type, integer2unsigned(whole_lhs_object_address));
}

void interpreter(
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  interpretert interpreter(
    symbol_table,
    goto_functions,
    message_handler);
  interpreter();
}

/// Prints the current state of the memory map Since messaget mdofifies class
/// members, print functions are nonconst
void interpretert::print_memory(bool input_flags)
{
  for(size_t i=0; i<memory.size(); i++)
  {
    memory_cellt &cell=memory[i];
    debug() << cell.identifier << "[" << cell.offset << "]"
            << "=" << cell.value << eom;
    if(input_flags)
      debug() << "(" << static_cast<int>(cell.initialized) << ")"
              << eom;
    debug() << eom;
  }
}
