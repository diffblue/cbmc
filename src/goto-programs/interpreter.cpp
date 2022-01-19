/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#include "interpreter.h"

#include <cctype>
#include <cstdio>
#include <fstream>
#include <algorithm>

#include <util/c_types.h>
#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_container.h>
#include <util/symbol_table.h>

#include "goto_model.h"
#include "interpreter_class.h"
#include "json_goto_trace.h"

const std::size_t interpretert::npos=std::numeric_limits<size_t>::max();

void interpretert::operator()()
{
  output.status() << "0- Initialize:" << messaget::eom;
  initialize(true);
  try
  {
    output.status() << "Type h for help\n" << messaget::eom;

    while(!done)
      command();

    output.status() << total_steps << "- Program End.\n" << messaget::eom;
  }
  catch (const char *e)
  {
    output.error() << e << "\n" << messaget::eom;
  }

  while(!done)
    command();
}

/// Initializes the memory map of the interpreter and [optionally] runs up to
/// the entry point (thus doing the cprover initialization)
void interpretert::initialize(bool init)
{
  build_memory_map();
  // reset the call stack
  call_stack = call_stackt{};

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
    // execute instructions up to and including __CPROVER_initialize()
    while(!done && call_stack.size() == 0)
    {
      show_state();
      step();
    }
    // initialization
    while(!done && call_stack.size() > 0)
    {
      show_state();
      step();
    }
    // invoke the user entry point
    while(!done && call_stack.size() == 0)
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
  output.status() << "\n"
                  << total_steps + 1
                  << " ----------------------------------------------------\n";

  if(pc==function->second.body.instructions.end())
  {
    output.status() << "End of function '" << function->first << "'\n";
  }
  else
    function->second.body.output_instruction(
      ns, function->first, output.status(), *pc);

  output.status() << messaget::eom;
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
    output.status() << "Interpreter help\n"
                    << "h: display this menu\n"
                    << "j: output json trace\n"
                    << "m: output memory dump\n"
                    << "o: output goto trace\n"
                    << "q: quit\n"
                    << "r: run up to entry point\n"
                    << "s#: step a number of instructions\n"
                    << "sa: step across a function\n"
                    << "so: step out of a function\n"
                    << "se: step until end of program\n"
                    << messaget::eom;
  }
  else if(ch=='j')
  {
    json_arrayt json_steps;
    convert<json_arrayt>(ns, steps, json_steps);
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
    json_steps.output(output.result());
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
    steps.output(ns, output.result());
  }
  else if(ch=='r')
  {
    ch=tolower(command[1]);
    initialize(ch!='0');
  }
  else if((ch=='s') || (ch==0))
  {
    num_steps=1;
    std::size_t stack_depth = npos;
    ch=tolower(command[1]);
    if(ch=='e')
      num_steps=npos;
    else if(ch=='o')
      stack_depth=call_stack.size();
    else if(ch=='a')
      stack_depth=call_stack.size()+1;
    else
    {
      num_steps = unsafe_string2size_t(command + 1);
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
  switch(pc->type())
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

  case SET_RETURN_VALUE:
    trace_step.type=goto_trace_stept::typet::FUNCTION_RETURN;
    if(call_stack.empty())
      throw "SET_RETURN_VALUE without call"; // NOLINT(readability/throw)

    if(call_stack.top().return_value_address != 0)
    {
      mp_vectort rhs = evaluate(pc->return_value());
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
    while(!done && (pc->type() != CATCH))
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
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    throw "encountered instruction with undefined instruction type";
  }
  pc=next_pc;
}

/// executes a goto instruction
void interpretert::execute_goto()
{
  if(evaluate_boolean(pc->get_condition()))
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
  const irep_idt &statement = pc->get_other().get_statement();
  if(statement==ID_expression)
  {
    DATA_INVARIANT(
      pc->get_code().operands().size() == 1,
      "expression statement expected to have one operand");
    mp_vectort rhs = evaluate(pc->get_code().op0());
  }
  else if(statement==ID_array_set)
  {
    mp_vectort tmp = evaluate(pc->get_code().op1());
    mp_integer address = evaluate_address(pc->get_code().op0());
    mp_integer size = get_size(pc->get_code().op0().type());
    mp_vectort rhs;
    while(rhs.size()<size) rhs.insert(rhs.end(), tmp.begin(), tmp.end());
    if(size!=rhs.size())
      output.error() << "!! failed to obtain rhs (" << rhs.size() << " vs. "
                     << size << ")\n"
                     << messaget::eom;
    else
    {
      assign(address, rhs);
    }
  }
  else if(can_cast_expr<code_outputt>(pc->get_other()))
  {
    return;
  }
  else
    throw "unexpected OTHER statement: "+id2string(statement);
}

void interpretert::execute_decl()
{
  PRECONDITION(pc->get_code().get_statement() == ID_decl);
}

/// Retrieves the member at \p offset of an object of type \p object_type.
struct_typet::componentt
interpretert::get_component(const typet &object_type, const mp_integer &offset)
{
  const typet real_type = ns.follow(object_type);
  if(real_type.id()!=ID_struct)
    throw "request for member of non-struct";

  const struct_typet &struct_type=to_struct_type(real_type);
  const struct_typet::componentst &components=struct_type.components();

  mp_integer tmp_offset=offset;

  for(const auto &c : components)
  {
    if(tmp_offset<=0)
      return c;

    tmp_offset-=get_size(c.type());
  }

  throw "access out of struct bounds";
}

/// returns the type object corresponding to id
typet interpretert::get_type(const irep_idt &id) const
{
  dynamic_typest::const_iterator it=dynamic_types.find(id);
  if(it==dynamic_types.end())
    return symbol_table.lookup_ref(id).type;
  return it->second;
}

/// retrives the constant value at memory location offset as an object of type
/// type
exprt interpretert::get_value(
  const typet &type,
  const mp_integer &offset,
  bool use_non_det)
{
  const typet real_type=ns.follow(type);
  if(real_type.id()==ID_struct)
  {
    struct_exprt result({}, real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();

    // Retrieve the values for the individual members
    result.reserve_operands(components.size());

    mp_integer tmp_offset=offset;

    for(const auto &c : components)
    {
      mp_integer size=get_size(c.type());
      const exprt operand=get_value(c.type(), tmp_offset);
      tmp_offset+=size;
      result.copy_to_operands(operand);
    }

    return std::move(result);
  }
  else if(real_type.id()==ID_array)
  {
    // Get size of array
    array_exprt result({}, to_array_type(real_type));
    const exprt &size_expr = to_array_type(type).size();
    mp_integer subtype_size = get_size(to_array_type(type).element_type());
    mp_integer count;
    if(size_expr.id()!=ID_constant)
    {
      count=base_address_to_actual_size(offset)/subtype_size;
    }
    else
    {
      count = numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
    }

    // Retrieve the value for each member in the array
    result.reserve_operands(numeric_cast_v<std::size_t>(count));
    for(mp_integer i=0; i<count; ++i)
    {
      const exprt operand = get_value(
        to_array_type(type).element_type(), offset + i * subtype_size);
      result.copy_to_operands(operand);
    }
    return std::move(result);
  }
  if(
    use_non_det && memory[numeric_cast_v<std::size_t>(offset)].initialized !=
                     memory_cellt::initializedt::WRITTEN_BEFORE_READ)
  {
    return side_effect_expr_nondett(type, source_locationt());
  }
  mp_vectort rhs;
  rhs.push_back(memory[numeric_cast_v<std::size_t>(offset)].value);
  return get_value(type, rhs);
}

/// returns the value at offset in the form of type given a memory buffer rhs
/// which is typically a structured type
exprt interpretert::get_value(
  const typet &type,
  mp_vectort &rhs,
  const mp_integer &offset)
{
  const typet real_type=ns.follow(type);
  PRECONDITION(!rhs.empty());

  if(real_type.id()==ID_struct)
  {
    struct_exprt result({}, real_type);
    const struct_typet &struct_type=to_struct_type(real_type);
    const struct_typet::componentst &components=struct_type.components();

    // Retrieve the values for the individual members
    result.reserve_operands(components.size());
    mp_integer tmp_offset=offset;

    for(const struct_union_typet::componentt &expr : components)
    {
      mp_integer size=get_size(expr.type());
      const exprt operand=get_value(expr.type(), rhs, tmp_offset);
      tmp_offset+=size;
      result.copy_to_operands(operand);
    }
    return std::move(result);
  }
  else if(real_type.id()==ID_array)
  {
    array_exprt result({}, to_array_type(real_type));
    const exprt &size_expr = to_array_type(real_type).size();

    // Get size of array
    mp_integer subtype_size = get_size(to_array_type(type).element_type());

    mp_integer count;
    if(unbounded_size(type))
    {
      count=base_address_to_actual_size(offset)/subtype_size;
    }
    else
    {
      count = numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
    }

    // Retrieve the value for each member in the array
    result.reserve_operands(numeric_cast_v<std::size_t>(count));
    for(mp_integer i=0; i<count; ++i)
    {
      const exprt operand = get_value(
        to_array_type(type).element_type(), rhs, offset + i * subtype_size);
      result.copy_to_operands(operand);
    }
    return std::move(result);
  }
  else if(real_type.id()==ID_floatbv)
  {
    ieee_floatt f(to_floatbv_type(type));
    f.unpack(rhs[numeric_cast_v<std::size_t>(offset)]);
    return f.to_expr();
  }
  else if(real_type.id()==ID_fixedbv)
  {
    fixedbvt f;
    f.from_integer(rhs[numeric_cast_v<std::size_t>(offset)]);
    return f.to_expr();
  }
  else if(real_type.id()==ID_bool)
  {
    if(rhs[numeric_cast_v<std::size_t>(offset)] != 0)
      return true_exprt();
    else
      false_exprt();
  }
  else if(real_type.id()==ID_c_bool)
  {
    return from_integer(
      rhs[numeric_cast_v<std::size_t>(offset)] != 0 ? 1 : 0, type);
  }
  else if(real_type.id() == ID_pointer)
  {
    if(rhs[numeric_cast_v<std::size_t>(offset)] == 0)
      return null_pointer_exprt(to_pointer_type(real_type)); // NULL pointer

    if(rhs[numeric_cast_v<std::size_t>(offset)] < memory.size())
    {
      // We want the symbol pointed to
      mp_integer address = rhs[numeric_cast_v<std::size_t>(offset)];
      const symbol_exprt &symbol_expr = address_to_symbol(address);
      mp_integer offset_from_address = address_to_offset(address);

      if(offset_from_address == 0)
        return address_of_exprt(symbol_expr);

      if(
        symbol_expr.type().id() == ID_struct ||
        symbol_expr.type().id() == ID_struct_tag)
      {
        const auto c = get_component(symbol_expr.type(), offset_from_address);
        member_exprt member_expr(symbol_expr, c);
        return address_of_exprt(member_expr);
      }

      return index_exprt(
        symbol_expr, from_integer(offset_from_address, integer_typet()));
    }

    output.error() << "interpreter: invalid pointer "
                   << rhs[numeric_cast_v<std::size_t>(offset)]
                   << " > object count " << memory.size() << messaget::eom;

    throw "interpreter: reading from invalid pointer";
  }
  else if(real_type.id()==ID_string)
  {
    // Strings are currently encoded by their irep_idt ID.
    return constant_exprt(
      get_string_container().get_string(
        numeric_cast_v<std::size_t>(rhs[numeric_cast_v<std::size_t>(offset)])),
      type);
  }

  // Retrieve value of basic data type
  return from_integer(rhs[numeric_cast_v<std::size_t>(offset)], type);
}

/// executes the assign statement at the current pc value
void interpretert::execute_assign()
{
  const exprt &assign_lhs = pc->assign_lhs();
  const exprt &assign_rhs = pc->assign_rhs();

  mp_vectort rhs = evaluate(assign_rhs);

  if(!rhs.empty())
  {
    mp_integer address = evaluate_address(assign_lhs);
    mp_integer size = get_size(assign_lhs.type());

    if(size!=rhs.size())
      output.error() << "!! failed to obtain rhs (" << rhs.size() << " vs. "
                     << size << ")\n"
                     << messaget::eom;
    else
    {
      goto_trace_stept &trace_step=steps.get_last_step();
      assign(address, rhs);
      trace_step.full_lhs = assign_lhs;
      trace_step.full_lhs_value=get_value(trace_step.full_lhs.type(), rhs);
    }
  }
  else if(assign_rhs.id() == ID_side_effect)
  {
    side_effect_exprt side_effect = to_side_effect_expr(assign_rhs);
    if(side_effect.get_statement()==ID_nondet)
    {
      mp_integer address =
        numeric_cast_v<std::size_t>(evaluate_address(assign_lhs));

      mp_integer size = get_size(assign_lhs.type());

      for(mp_integer i=0; i<size; ++i)
      {
        memory[numeric_cast_v<std::size_t>(address + i)].initialized =
          memory_cellt::initializedt::READ_BEFORE_WRITTEN;
      }
    }
  }
}

/// sets the memory at address with the given rhs value (up to sizeof(rhs))
void interpretert::assign(
  const mp_integer &address,
  const mp_vectort &rhs)
{
  for(mp_integer i=0; i<rhs.size(); ++i)
  {
    if((address+i)<memory.size())
    {
      mp_integer address_val=address+i;
      memory_cellt &cell = memory[numeric_cast_v<std::size_t>(address_val)];
      if(show)
      {
        output.status() << total_steps << " ** assigning "
                        << address_to_symbol(address_val).get_identifier()
                        << "[" << address_to_offset(address_val)
                        << "]:=" << rhs[numeric_cast_v<std::size_t>(i)] << "\n"
                        << messaget::eom;
      }
      cell.value = rhs[numeric_cast_v<std::size_t>(i)];
      if(cell.initialized==memory_cellt::initializedt::UNKNOWN)
        cell.initialized=memory_cellt::initializedt::WRITTEN_BEFORE_READ;
    }
  }
}

void interpretert::execute_assume()
{
  if(!evaluate_boolean(pc->get_condition()))
    throw "assumption failed";
}

void interpretert::execute_assert()
{
  if(!evaluate_boolean(pc->get_condition()))
  {
    if(show)
      output.error() << "assertion failed at " << pc->location_number << "\n"
                     << messaget::eom;
  }
}

void interpretert::execute_function_call()
{
  const auto &call_lhs = pc->call_lhs();
  const auto &call_function = pc->call_function();
  const auto &call_arguments = pc->call_arguments();

  // function to be called
  mp_integer address = evaluate_address(call_function);

  if(address==0)
    throw "function call to NULL";
  else if(address>=memory.size())
    throw "out-of-range function call";

  // Retrieve the empty last trace step struct we pushed for this step
  // of the interpreter run to fill it with the corresponding data
  goto_trace_stept &trace_step=steps.get_last_step();
#if 0
  const memory_cellt &cell=memory[address];
#endif
  const irep_idt &identifier = address_to_symbol(address).get_identifier();
  trace_step.called_function = identifier;

  const goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(identifier);

  if(f_it==goto_functions.function_map.end())
    throw "failed to find function "+id2string(identifier);

  // return value
  mp_integer return_value_address;

  if(call_lhs.is_not_nil())
    return_value_address = evaluate_address(call_lhs);
  else
    return_value_address=0;

  // values of the arguments
  std::vector<mp_vectort> argument_values;

  argument_values.resize(call_arguments.size());

  for(std::size_t i = 0; i < call_arguments.size(); i++)
    argument_values[i] = evaluate(call_arguments[i]);

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
      frame.local_map[id] = build_memory_map(symbol.symbol_expr());
    }

    // assign the arguments
    const auto &parameter_identifiers = f_it->second.parameter_identifiers;
    if(argument_values.size() < parameter_identifiers.size())
      throw "not enough arguments";

    for(std::size_t i = 0; i < parameter_identifiers.size(); i++)
    {
      const symbol_exprt symbol_expr =
        ns.lookup(parameter_identifiers[i]).symbol_expr();
      assign(evaluate_address(symbol_expr), argument_values[i]);
    }

    // set up new pc
    function=f_it;
    next_pc=f_it->second.body.instructions.begin();
  }
  else
  {
    list_input_varst::iterator it =
      function_input_vars.find(to_symbol_expr(call_function).get_identifier());

    if(it!=function_input_vars.end())
    {
      PRECONDITION(!it->second.empty());
      PRECONDITION(!it->second.front().return_assignments.empty());
      mp_vectort value =
        evaluate(it->second.front().return_assignments.back().value);
      if(return_value_address>0)
      {
        assign(return_value_address, value);
      }
      it->second.pop_front();
      return;
    }

    if(show)
      output.error() << "no body for " << identifier << messaget::eom;
  }
}

/// Creates a memory map of all static symbols in the program
void interpretert::build_memory_map()
{
  // put in a dummy for NULL
  memory.clear();
  memory.resize(1);
  inverse_memory_map[0] = {};

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
  mp_integer size=0;

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
    mp_integer address=memory.size();
    memory.resize(numeric_cast_v<std::size_t>(address + size));
    memory_map[symbol.name]=address;
    inverse_memory_map[address] = symbol.symbol_expr();
  }
}

/// turns a variable length array type into a fixed array type
typet interpretert::concretize_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const exprt &size_expr = to_array_type(type).size();
    mp_vectort computed_size = evaluate(size_expr);
    if(computed_size.size()==1 &&
       computed_size[0]>=0)
    {
      output.result() << "Concretized array with size " << computed_size[0]
                      << messaget::eom;
      return array_typet(
        to_array_type(type).element_type(),
        from_integer(computed_size[0], integer_typet()));
    }
    else
    {
      output.warning() << "Failed to concretize variable array"
                       << messaget::eom;
    }
  }
  return type;
}

/// Populates dynamic entries of the memory map
/// \return Updates the memory map to include variable id if it does not exist
mp_integer interpretert::build_memory_map(const symbol_exprt &symbol_expr)
{
  typet alloc_type = concretize_type(symbol_expr.type());
  mp_integer size=get_size(alloc_type);
  auto it = dynamic_types.find(symbol_expr.get_identifier());

  if(it!=dynamic_types.end())
  {
    mp_integer address = memory_map[symbol_expr.get_identifier()];
    mp_integer current_size=base_address_to_alloc_size(address);
    // current size <= size already recorded
    if(size<=current_size)
      return memory_map[symbol_expr.get_identifier()];
  }

  // The current size is bigger then the one previously recorded
  // in the memory map

  if(size==0)
    size=1; // This is a hack to create existence

  mp_integer address=memory.size();
  memory.resize(numeric_cast_v<std::size_t>(address + size));
  memory_map[symbol_expr.get_identifier()] = address;
  inverse_memory_map[address] = symbol_expr;
  dynamic_types.insert(
    std::pair<const irep_idt, typet>(symbol_expr.get_identifier(), alloc_type));

  return address;
}

bool interpretert::unbounded_size(const typet &type)
{
  if(type.id()==ID_array)
  {
    const exprt &size=to_array_type(type).size();
    if(size.id()==ID_infinity)
      return true;
    return unbounded_size(to_array_type(type).element_type());
  }
  else if(type.id()==ID_struct)
  {
    const auto &st=to_struct_type(type);
    if(st.components().empty())
      return false;
    return unbounded_size(st.components().back().type());
  }
  return false;
}

/// Retrieves the actual size of the provided structured type. Unbounded objects
/// get allocated 2^32 address space each (of a 2^64 sized space).
/// \param type: a structured type
/// \return Size of the given type
mp_integer interpretert::get_size(const typet &type)
{
  if(unbounded_size(type))
    return mp_integer(2) << 32;

  if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    mp_integer sum=0;

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

    mp_integer max_size=0;

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
    const exprt &size_expr = to_array_type(type).size();

    mp_integer subtype_size = get_size(to_array_type(type).element_type());

    mp_vectort i = evaluate(size_expr);
    if(i.size()==1)
    {
      // Go via the binary representation to reproduce any
      // overflow behaviour.
      const constant_exprt size_const = from_integer(i[0], size_expr.type());
      const mp_integer size_mp = numeric_cast_v<mp_integer>(size_const);
      return subtype_size*size_mp;
    }
    return subtype_size;
  }
  else if(type.id() == ID_struct_tag)
  {
    return get_size(ns.follow_tag(to_struct_tag_type(type)));
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
    get_type=symbol_table.lookup_ref(id).type;

  symbol_exprt symbol_expr(id, get_type);
  mp_integer whole_lhs_object_address=evaluate_address(symbol_expr);

  return get_value(get_type, whole_lhs_object_address);
}

/// Prints the current state of the memory map Since messaget mdofifies class
/// members, print functions are nonconst
void interpretert::print_memory(bool input_flags)
{
  for(const auto &cell_address : memory)
  {
    mp_integer i=cell_address.first;
    const memory_cellt &cell=cell_address.second;
    const auto identifier = address_to_symbol(i).get_identifier();
    const auto offset=address_to_offset(i);
    output.status() << identifier << "[" << offset << "]"
                    << "=" << cell.value << messaget::eom;
    if(input_flags)
      output.status() << "(" << static_cast<int>(cell.initialized) << ")"
                      << messaget::eom;
    output.status() << messaget::eom;
  }
}

void interpreter(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  interpretert interpreter(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
  interpreter();
}
