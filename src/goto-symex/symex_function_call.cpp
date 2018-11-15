/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/invariant.h>

bool goto_symext::get_unwind_recursion(
  const irep_idt &,
  const unsigned,
  unsigned)
{
  return false;
}

void goto_symext::parameter_assignments(
  const irep_idt &function_identifier,
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

    INVARIANT(
      !identifier.empty(),
      "function pointer parameter must have an identifier");

    const symbolt &symbol=ns.lookup(identifier);
    symbol_exprt lhs=symbol.symbol_expr();

    exprt rhs;

    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      log.warning() << state.source.pc->source_location.as_string()
                    << ": "
                       "call to `"
                    << id2string(function_identifier)
                    << "': "
                       "not enough arguments, inserting non-deterministic value"
                    << log.eom;

      rhs = side_effect_expr_nondett(
        parameter_type, state.source.pc->source_location);
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
              from_integer(0, index_type()),
              parameter_type);
        }
        else
        {
          std::ostringstream error;
          error << "function call: parameter \"" << identifier
                << "\" type mismatch: got " << rhs.type().pretty()
                << ", expected " << parameter_type.pretty();
          throw unsupported_operation_exceptiont(error.str());
        }
      }

      symex_assign(state, code_assignt(lhs, rhs));
    }

    if(it1!=arguments.end())
      it1++;
  }

  if(function_type.has_ellipsis())
  {
    // These are va_arg arguments; their types may differ from call to call
    std::size_t va_count=0;
    const symbolt *va_sym=nullptr;
    while(!ns.lookup(
        id2string(function_identifier)+"::va_arg"+std::to_string(va_count),
        va_sym))
      ++va_count;

    for( ; it1!=arguments.end(); it1++, va_count++)
    {
      irep_idt id=
        id2string(function_identifier)+"::va_arg"+std::to_string(va_count);

      // add to symbol table
      symbolt symbol;
      symbol.name=id;
      symbol.base_name="va_arg"+std::to_string(va_count);
      symbol.mode=ID_C;
      symbol.type=it1->type();

      state.symbol_table.insert(std::move(symbol));

      symbol_exprt lhs=symbol_exprt(id, it1->type());

      symex_assign(state, code_assignt(lhs, *it1));
    }
  }
  else if(it1!=arguments.end())
  {
    // we got too many arguments, but we will just ignore them
  }
}

void goto_symext::symex_function_call(
  const get_goto_functiont &get_goto_function,
  statet &state,
  const code_function_callt &code)
{
  const exprt &function=code.function();

  // If at some point symex_function_call can support more
  // expression ids(), like ID_Dereference, please expand the
  // precondition appropriately.
  PRECONDITION(function.id() == ID_symbol);
  symex_function_call_symbol(get_goto_function, state, code);
}

void goto_symext::symex_function_call_symbol(
  const get_goto_functiont &get_goto_function,
  statet &state,
  const code_function_callt &code)
{
  target.location(state.guard.as_expr(), state.source);

  PRECONDITION(code.function().id() == ID_symbol);

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
    symex_function_call_code(get_goto_function, state, code);
}

/// do function call by inlining
void goto_symext::symex_function_call_code(
  const get_goto_functiont &get_goto_function,
  statet &state,
  const code_function_callt &call)
{
  const irep_idt &identifier=
    to_symbol_expr(call.function()).get_identifier();

  const goto_functionst::goto_functiont &goto_function =
    get_goto_function(identifier);

  state.dirty.populate_dirty_for_function(identifier, goto_function);

  auto emplace_safe_pointers_result =
    state.safe_pointers.emplace(identifier, local_safe_pointerst{ns});
  if(emplace_safe_pointers_result.second)
    emplace_safe_pointers_result.first->second(goto_function.body);

  const bool stop_recursing=get_unwind_recursion(
    identifier,
    state.source.thread_nr,
    state.top().loop_iterations[identifier].count);

  // see if it's too much
  if(stop_recursing)
  {
    if(partial_loops)
    {
      // it's ok, ignore
    }
    else
    {
      if(unwinding_assertions)
        vcc(false_exprt(), "recursion unwinding assertion", state);

      // add to state guard to prevent further assignments
      state.guard.add(false_exprt());
    }

    symex_transition(state);
    return;
  }

  // read the arguments -- before the locality renaming
  exprt::operandst arguments = call.arguments();
  for(auto &a : arguments)
    state.rename(a, ns);

  // record the call
  target.function_call(
    state.guard.as_expr(), identifier, arguments, state.source);

  if(!goto_function.body_available())
  {
    no_body(identifier);

    // record the return
    target.function_return(state.guard.as_expr(), state.source);

    if(call.lhs().is_not_nil())
    {
      const auto rhs =
        side_effect_expr_nondett(call.lhs().type(), call.source_location());
      code_assignt code(call.lhs(), rhs);
      symex_assign(state, code);
    }

    symex_transition(state);
    return;
  }

  // produce a new frame
  PRECONDITION(!state.call_stack().empty());
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
  state.source.function = identifier;
  symex_transition(state, goto_function.body.instructions.begin(), false);
}

/// pop one call frame
void goto_symext::pop_frame(statet &state)
{
  PRECONDITION(!state.call_stack().empty());

  {
    statet::framet &frame=state.top();

    // restore program counter
    symex_transition(state, frame.calling_location.pc, false);
    state.source.function = frame.calling_location.function;

    // restore L1 renaming
    state.level1.restore_from(frame.old_level1);

    // clear function-locals from L2 renaming
    for(renaming_levelt::current_namest::iterator c_it =
          state.level2.current_names.begin();
        c_it != state.level2.current_names.end();) // no ++c_it
    {
      const irep_idt l1_o_id=c_it->second.first.get_l1_object_identifier();
      // could use iteration over local_objects as l1_o_id is prefix
      if(
        frame.local_objects.find(l1_o_id) == frame.local_objects.end() ||
        (state.threads.size() > 1 &&
         state.dirty(c_it->second.first.get_object_name())))
      {
        ++c_it;
        continue;
      }
      renaming_levelt::current_namest::iterator cur = c_it;
      ++c_it;
      state.level2.current_names.erase(cur);
    }
  }

  state.pop_frame();
}

/// do function call by inlining
void goto_symext::symex_end_of_function(statet &state)
{
  // first record the return
  target.function_return(state.guard.as_expr(), state.source);

  // then get rid of the frame
  pop_frame(state);
}

/// preserves locality of local variables of a given function by applying L1
/// renaming to the local identifiers
void goto_symext::locality(
  const irep_idt &function_identifier,
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
    symex_level1t::current_namest::const_iterator c_it =
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

void goto_symext::return_assignment(statet &state)
{
  statet::framet &frame=state.top();

  const goto_programt::instructiont &instruction=*state.source.pc;
  PRECONDITION(instruction.is_return());
  const code_returnt &code=to_code_return(instruction.code);

  target.location(state.guard.as_expr(), state.source);

  PRECONDITION(code.operands().size() == 1 || frame.return_value.is_nil());

  exprt value = code.return_value();

  if(frame.return_value.is_not_nil())
  {
    code_assignt assignment(frame.return_value, value);

    INVARIANT(
      base_type_eq(assignment.lhs().type(), assignment.rhs().type(), ns),
      "goto_symext::return_assignment type mismatch");

    symex_assign(state, assignment);
  }
}
