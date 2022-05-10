/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/range.h>
#include <util/std_code.h>

#include "expr_skeleton.h"
#include "path_storage.h"
#include "symex_assign.h"

static void locality(
  const irep_idt &function_identifier,
  goto_symext::statet &state,
  path_storaget &path_storage,
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns);

bool goto_symext::get_unwind_recursion(const irep_idt &, unsigned, unsigned)
{
  return false;
}

void goto_symext::parameter_assignments(
  const irep_idt &function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  statet &state,
  const exprt::operandst &arguments)
{
  // iterates over the arguments
  exprt::operandst::const_iterator it1=arguments.begin();

  // iterates over the types of the parameters
  for(const auto &identifier : goto_function.parameter_identifiers)
  {
    INVARIANT(
      !identifier.empty(), "function parameter must have an identifier");
    state.call_stack().top().parameter_names.push_back(identifier);

    const symbolt &symbol=ns.lookup(identifier);
    symbol_exprt lhs=symbol.symbol_expr();

    // this is the type that the n-th argument should have
    const typet &parameter_type = symbol.type;

    exprt rhs;

    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      log.warning() << state.source.pc->source_location().as_string()
                    << ": "
                       "call to '"
                    << id2string(function_identifier)
                    << "': "
                       "not enough arguments, inserting non-deterministic value"
                    << log.eom;

      rhs = side_effect_expr_nondett(
        parameter_type, state.source.pc->source_location());
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
      if(parameter_type != rhs.type())
      {
        const typet &rhs_type = rhs.type();

        // But we are willing to do some limited conversion.
        // This is highly dubious, obviously.
        // clang-format off
        if(
          (parameter_type.id() == ID_signedbv ||
           parameter_type.id() == ID_unsignedbv ||
           parameter_type.id() == ID_c_enum_tag ||
           parameter_type.id() == ID_bool ||
           parameter_type.id() == ID_pointer ||
           parameter_type.id() == ID_union ||
           parameter_type.id() == ID_union_tag) &&
          (rhs_type.id() == ID_signedbv ||
           rhs_type.id() == ID_unsignedbv ||
           rhs_type.id() == ID_c_bit_field ||
           rhs_type.id() == ID_c_enum_tag ||
           rhs_type.id() == ID_bool ||
           rhs_type.id() == ID_pointer ||
           rhs_type.id() == ID_union ||
           rhs_type.id() == ID_union_tag))
        // clang-format on
        {
          rhs = make_byte_extract(
            rhs, from_integer(0, c_index_type()), parameter_type);
        }
        else
        {
          std::ostringstream error;
          error << state.source.pc->source_location().as_string() << ": "
                << "function call: parameter \"" << identifier
                << "\" type mismatch:\ngot " << rhs.type().pretty()
                << "\nexpected " << parameter_type.pretty();
          throw unsupported_operation_exceptiont(error.str());
        }
      }

      assignment_typet assignment_type;

      // We hide if we are in a hidden function.
      if(state.call_stack().top().hidden_function)
        assignment_type =
          symex_targett::assignment_typet::HIDDEN_ACTUAL_PARAMETER;
      else
        assignment_type =
          symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER;

      lhs = to_symbol_expr(clean_expr(std::move(lhs), state, true));
      rhs = clean_expr(std::move(rhs), state, false);

      exprt::operandst lhs_conditions;
      symex_assignt{state, assignment_type, ns, symex_config, target}
        .assign_rec(lhs, expr_skeletont{}, rhs, lhs_conditions);
    }

    if(it1!=arguments.end())
      it1++;
  }

  if(to_code_type(ns.lookup(function_identifier).type).has_ellipsis())
  {
    // These are va_arg arguments; their types may differ from call to call
    for(; it1 != arguments.end(); it1++)
    {
      symbolt &va_arg = get_fresh_aux_symbol(
        it1->type(),
        id2string(function_identifier),
        "va_arg",
        state.source.pc->source_location(),
        ns.lookup(function_identifier).mode,
        state.symbol_table);
      va_arg.is_parameter = true;

      state.call_stack().top().parameter_names.push_back(va_arg.name);

      symex_assign(state, va_arg.symbol_expr(), *it1);
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
  const goto_programt::instructiont &instruction)
{
  const exprt &function = instruction.call_function();

  // If at some point symex_function_call can support more
  // expression ids(), like ID_Dereference, please expand the
  // precondition appropriately.
  PRECONDITION(function.id() == ID_symbol);

  symex_function_call_symbol(
    get_goto_function,
    state,
    instruction.call_lhs(),
    to_symbol_expr(instruction.call_function()),
    instruction.call_arguments());
}

void goto_symext::symex_function_call_symbol(
  const get_goto_functiont &get_goto_function,
  statet &state,
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments)
{
  exprt cleaned_lhs;

  if(lhs.is_nil())
    cleaned_lhs = lhs;
  else
    cleaned_lhs = clean_expr(lhs, state, true);

  // no need to clean the function, which is a symbol only

  exprt::operandst cleaned_arguments;

  for(auto &argument : arguments)
    cleaned_arguments.push_back(clean_expr(argument, state, false));

  target.location(state.guard.as_expr(), state.source);

  symex_function_call_post_clean(
    get_goto_function, state, cleaned_lhs, function, cleaned_arguments);
}

void goto_symext::symex_function_call_post_clean(
  const get_goto_functiont &get_goto_function,
  statet &state,
  const exprt &cleaned_lhs,
  const symbol_exprt &function,
  const exprt::operandst &cleaned_arguments)
{
  const irep_idt &identifier = function.get_identifier();

  const goto_functionst::goto_functiont &goto_function =
    get_goto_function(identifier);

  path_storage.dirty.populate_dirty_for_function(identifier, goto_function);

  auto emplace_safe_pointers_result =
    path_storage.safe_pointers.emplace(identifier, local_safe_pointerst{});
  if(emplace_safe_pointers_result.second)
    emplace_safe_pointers_result.first->second(goto_function.body);

  const bool stop_recursing = get_unwind_recursion(
    identifier,
    state.source.thread_nr,
    state.call_stack().top().loop_iterations[identifier].count);

  // see if it's too much
  if(stop_recursing)
  {
    if(symex_config.unwinding_assertions)
      vcc(false_exprt(), "recursion unwinding assertion", state);
    if(!symex_config.partial_loops)
    {
      // Rule out this path:
      symex_assume_l2(state, false_exprt());
    }

    symex_transition(state);
    return;
  }

  // read the arguments -- before the locality renaming
  const std::vector<renamedt<exprt, L2>> renamed_arguments =
    make_range(cleaned_arguments).map([&](const exprt &a) {
      return state.rename(a, ns);
    });

  // we hide the call if the caller and callee are both hidden
  const bool hidden =
    state.call_stack().top().hidden_function && goto_function.is_hidden();

  // record the call
  target.function_call(
    state.guard.as_expr(), identifier, renamed_arguments, state.source, hidden);

  if(!goto_function.body_available())
  {
    no_body(identifier);

    // record the return
    target.function_return(
      state.guard.as_expr(), identifier, state.source, hidden);

    if(cleaned_lhs.is_not_nil())
    {
      const auto rhs = side_effect_expr_nondett(
        cleaned_lhs.type(), state.source.pc->source_location());
      symex_assign(state, cleaned_lhs, rhs);
    }

    if(symex_config.havoc_undefined_functions)
    {
      // assign non det to function arguments if pointers
      // are not const
      for(const auto &arg : cleaned_arguments)
      {
        if(
          arg.type().id() == ID_pointer &&
          !to_pointer_type(arg.type()).base_type().get_bool(ID_C_constant) &&
          to_pointer_type(arg.type()).base_type().id() != ID_code)
        {
          exprt object =
            dereference_exprt(arg, to_pointer_type(arg.type()).base_type());
          exprt cleaned_object = clean_expr(object, state, true);
          const guardt guard(true_exprt(), state.guard_manager);
          havoc_rec(state, guard, cleaned_object);
        }
      }
    }

    symex_transition(state);
    return;
  }

  // produce a new frame
  PRECONDITION(!state.call_stack().empty());
  framet &frame = state.call_stack().new_frame(state.source, state.guard);

  // Only enable loop analysis when complexity is enabled.
  if(symex_config.complexity_limits_active)
  {
    // Analyzes loops if required.
    path_storage.add_function_loops(identifier, goto_function.body);
    frame.loops_info = path_storage.get_loop_analysis(identifier);
  }

  // preserve locality of local variables
  locality(identifier, state, path_storage, goto_function, ns);

  // assign actuals to formal parameters
  parameter_assignments(identifier, goto_function, state, cleaned_arguments);

  frame.call_lhs = cleaned_lhs;
  frame.end_of_function = --goto_function.body.instructions.end();
  frame.function_identifier=identifier;
  frame.hidden_function = goto_function.is_hidden();

  // set up the 'return value symbol' when needed
  if(frame.call_lhs.is_not_nil())
  {
    irep_idt return_value_symbol_identifier =
      "goto_symex::return_value::" + id2string(identifier);

    if(!state.symbol_table.has_symbol(return_value_symbol_identifier))
    {
      const symbolt &function_symbol = ns.lookup(identifier);
      auxiliary_symbolt
        new_symbol; // these are thread-local and have dynamic lifetime
      new_symbol.base_name = "return_value";
      new_symbol.name = return_value_symbol_identifier;
      new_symbol.type = to_code_type(function_symbol.type).return_type();
      new_symbol.mode = function_symbol.mode;
      state.symbol_table.add(new_symbol);
    }

    frame.return_value_symbol =
      ns.lookup(return_value_symbol_identifier).symbol_expr();
  }

  const framet &p_frame = state.call_stack().previous_frame();
  for(const auto &pair : p_frame.loop_iterations)
  {
    if(pair.second.is_recursion)
      frame.loop_iterations.insert(pair);
  }

  // increase unwinding counter
  frame.loop_iterations[identifier].is_recursion=true;
  frame.loop_iterations[identifier].count++;

  state.source.function_id = identifier;
  symex_transition(state, goto_function.body.instructions.begin(), false);
}

/// pop one call frame
static void pop_frame(
  goto_symext::statet &state,
  const path_storaget &path_storage,
  bool doing_path_exploration)
{
  PRECONDITION(!state.call_stack().empty());

  const framet &frame = state.call_stack().top();

  // restore program counter
  symex_transition(state, frame.calling_location.pc, false);
  state.source.function_id = frame.calling_location.function_id;

  // restore L1 renaming
  state.level1.restore_from(frame.old_level1);

  // If the program is multi-threaded then the state guard is used to
  // accumulate assumptions (in symex_assume_l2) and must be left alone.
  // If however it is single-threaded then we should restore the guard, as the
  // guard coming out of the function may be more complex (e.g. if the callee
  // was { if(x) while(true) { } } then the guard may still be `!x`),
  // but at this point all control-flow paths have either converged or been
  // proven unviable, so we can stop specifying the callee's constraints when
  // we generate an assumption or VCC.

  // If we're doing path exploration then we do tail-duplication, and we
  // actually *are* in a more-restricted context than we were when the
  // function began.
  if(state.threads.size() == 1 && !doing_path_exploration)
  {
    state.guard = frame.guard_at_function_start;
  }

  for(const irep_idt &l1_o_id : frame.local_objects)
  {
    const auto l2_entry_opt = state.get_level2().current_names.find(l1_o_id);

    if(
      l2_entry_opt.has_value() &&
      (state.threads.size() == 1 ||
       !path_storage.dirty(l2_entry_opt->get().first.get_object_name())))
    {
      state.drop_existing_l1_name(l1_o_id);
    }
  }

  state.call_stack().pop();
}

/// do function call by inlining
void goto_symext::symex_end_of_function(statet &state)
{
  PRECONDITION(!state.call_stack().empty());

  const bool hidden = state.call_stack().top().hidden_function;

  // first record the return
  target.function_return(
    state.guard.as_expr(), state.source.function_id, state.source, hidden);

  // before we drop the frame, remember the call LHS
  // and the return value symbol, if any
  auto call_lhs = state.call_stack().top().call_lhs;
  auto return_value_symbol = state.call_stack().top().return_value_symbol;

  // now get rid of the frame
  pop_frame(state, path_storage, symex_config.doing_path_exploration);

  // after dropping the frame, assign the return value, if any
  if(state.reachable && call_lhs.is_not_nil())
  {
    DATA_INVARIANT(
      return_value_symbol.has_value(),
      "must have return value symbol when assigning call lhs");
    // the type of the call lhs and the return type might not match
    auto casted_return_value = typecast_exprt::conditional_cast(
      return_value_symbol.value(), call_lhs.type());
    symex_assign(state, call_lhs, casted_return_value);
  }
}

/// Preserves locality of parameters of a given function by applying L1
/// renaming to them.
static void locality(
  const irep_idt &function_identifier,
  goto_symext::statet &state,
  path_storaget &path_storage,
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  unsigned &frame_nr=
    state.threads[state.source.thread_nr].function_frame[function_identifier];
  frame_nr++;

  for(const auto &param : goto_function.parameter_identifiers)
  {
    (void)state.add_object(
      ns.lookup(param).symbol_expr(),
      [&path_storage, &frame_nr](const irep_idt &l0_name) {
        return path_storage.get_unique_l1_index(l0_name, frame_nr);
      },
      ns);
  }
}
