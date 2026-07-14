/*******************************************************************\

Module: Remove exceptions (language-agnostic goto-level lowering)

Author: Cristina David (Java), Kiro (base extraction)

\*******************************************************************/

/// \file
/// Language-agnostic base for lowering exceptions to gotos/assignments.

#include "remove_exceptions_base.h"

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_skip.h>

#include <analyses/uncaught_exceptions_analysis.h>

bool remove_exceptions_baset::function_or_callees_may_throw(
  const goto_programt &goto_program) const
{
  for(const auto &instruction : goto_program.instructions)
  {
    if(instruction.is_throw())
      return true;

    if(instruction.is_function_call())
    {
      const exprt &function_expr = instruction.call_function();
      DATA_INVARIANT(
        function_expr.id() == ID_symbol, "identifier expected to be a symbol");
      const irep_idt &function_name =
        to_symbol_expr(function_expr).identifier();
      if(function_may_throw(function_name))
        return true;
    }
  }

  return false;
}

goto_programt::targett remove_exceptions_baset::find_universal_exception(
  const stack_catcht &stack_catch,
  goto_programt &goto_program,
  std::size_t &universal_try,
  std::size_t &universal_catch)
{
  for(std::size_t i = stack_catch.size(); i > 0;)
  {
    i--;
    for(std::size_t j = 0; j < stack_catch[i].size(); ++j)
    {
      if(stack_catch[i][j].first.empty())
      {
        // The innermost universal (catch(...)) handler: no handler after it
        // can catch, so this is the default dispatch target.
        universal_try = i;
        universal_catch = j;
        return stack_catch[i][j].second;
      }
    }
  }
  // No universal handler: escape to the end of the function.
  return goto_program.get_end_function();
}

void remove_exceptions_baset::add_exception_dispatch_sequence(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const stack_catcht &stack_catch,
  const std::vector<symbol_exprt> &locals)
{
  // If the innermost try level carries an exceptional-exit landing (emitted by
  // the C++ goto conversion), propagate level by level: dispatch only this
  // level's handlers, and route an unmatched exception to the exceptional
  // exit, which runs the destructors of the scopes between this try and the
  // enclosing one ([except.ctor]) and then re-dispatches at the enclosing
  // level.  A flat multi-level dispatch would jump straight to an outer
  // handler, skipping those destructors.
  std::optional<goto_programt::targett> exceptional_exit;
  if(!stack_catch.empty())
  {
    for(const auto &handler : stack_catch.back())
    {
      if(handler.first == EXCEPTIONAL_EXIT_TAG)
        exceptional_exit = handler.second;
    }
  }

  if(exceptional_exit.has_value())
  {
    // The default jump appears after the dynamic dispatch gotos inserted
    // below.  It goes to this level's universal handler (catch(...), the last
    // handler if present, [except.handle]) or else to the exceptional exit.
    goto_programt::targett default_dispatch =
      goto_program.insert_after(instr_it);

    const catch_handlerst &handlers = stack_catch.back();
    goto_programt::targett default_target = *exceptional_exit;

    for(const auto &handler : handlers)
    {
      if(handler.first.empty()) // universal handler, catch(...)
      {
        default_target = handler.second;
        if(prepared_handlers.insert(&*default_target).second)
          prepare_handler(goto_program, default_target);
      }
    }

    // Reversed because each insertion is placed immediately after instr_it,
    // reversing program order.
    for(std::size_t j = handlers.size(); j > 0;)
    {
      j--;
      if(handlers[j].first.empty() || handlers[j].first == EXCEPTIONAL_EXIT_TAG)
        continue;
      const goto_programt::targett new_state_pc = handlers[j].second;
      if(prepared_handlers.insert(&*new_state_pc).second)
        prepare_handler(goto_program, new_state_pc);
      add_handler_dispatch(
        function_identifier,
        goto_program,
        instr_it,
        handlers[j].first,
        new_state_pc);
    }

    *default_dispatch = goto_programt::make_goto(
      default_target, true_exprt(), instr_it->source_location());

    // add dead instructions
    for(const auto &local : locals)
    {
      goto_program.insert_after(
        instr_it, goto_programt::make_dead(local, instr_it->source_location()));
    }
    return;
  }

  // Jump to the universal handler or function end, as appropriate.  This
  // appears after the dynamic dispatch gotos inserted below.
  goto_programt::targett default_dispatch = goto_program.insert_after(instr_it);

  std::size_t default_try = 0;
  std::size_t default_catch =
    (!stack_catch.empty()) ? stack_catch[0].size() : 0;

  goto_programt::targett default_target = find_universal_exception(
    stack_catch, goto_program, default_try, default_catch);

  // Emit the per-handler dispatch gotos.  The outer loop is forward and the
  // inner loop is reversed because each insertion is placed immediately after
  // instr_it, reversing program order.
  for(std::size_t i = default_try; i < stack_catch.size(); i++)
  {
    for(std::size_t j = (i == default_try) ? default_catch
                                           : stack_catch[i].size();
        j > 0;)
    {
      j--;
      const goto_programt::targett new_state_pc = stack_catch[i][j].second;
      if(!stack_catch[i][j].first.empty())
      {
        if(prepared_handlers.insert(&*new_state_pc).second)
          prepare_handler(goto_program, new_state_pc);
        add_handler_dispatch(
          function_identifier,
          goto_program,
          instr_it,
          stack_catch[i][j].first,
          new_state_pc);
      }
    }
  }

  // The universal handler (catch(...)), if any, may still bind/clear.
  if(
    default_target != goto_program.get_end_function() &&
    prepared_handlers.insert(&*default_target).second)
  {
    prepare_handler(goto_program, default_target);
  }

  *default_dispatch = goto_programt::make_goto(
    default_target, true_exprt(), instr_it->source_location());

  // add dead instructions
  for(const auto &local : locals)
  {
    goto_program.insert_after(
      instr_it, goto_programt::make_dead(local, instr_it->source_location()));
  }
}

bool remove_exceptions_baset::instrument_throw(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const stack_catcht &stack_catch,
  const std::vector<symbol_exprt> &locals)
{
  PRECONDITION(instr_it->type() == THROW);

  add_exception_dispatch_sequence(
    function_identifier, goto_program, instr_it, stack_catch, locals);

  // A propagate marker (the tail of an exceptional-exit landing) re-dispatches
  // an exception that is already in flight; the in-flight state must be left
  // untouched.  Only a real THROW records its thrown value.
  const codet &code = instr_it->code();
  const bool is_propagate = code.get_statement() == ID_expression &&
                            code.op0().id() == ID_side_effect &&
                            code.op0().get_bool("#exception_propagate");

  if(is_propagate)
    instr_it->turn_into_skip();
  else
  {
    // record the thrown value as the in-flight exception (language-specific)
    set_inflight_exception(goto_program, instr_it);
  }

  return true;
}

remove_exceptions_baset::instrumentation_resultt
remove_exceptions_baset::instrument_function_call(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const stack_catcht &stack_catch,
  const std::vector<symbol_exprt> &locals)
{
  PRECONDITION(instr_it->type() == FUNCTION_CALL);

  // A call-site unwind cleanup follows this call (emitted by the C++ goto
  // conversion): it runs the pending destructors and ends in a
  // propagate-marker THROW whose dispatch replaces the one we would insert
  // here.  Adding a dispatch here as well would jump to a handler before
  // those destructors have run.
  if(instr_it->code().get_bool("#cpp_unwind_cleanup_follows"))
    return instrumentation_resultt::DID_NOTHING;

  // A destructor call on an exceptional unwind path (emitted by the C++ goto
  // conversion): an exception is in flight by construction, so an in-flight
  // dispatch here would jump to a handler mid-unwind and skip the remaining
  // destructors.  A destructor that throws during unwinding terminates
  // ([except.terminate]).
  if(instr_it->code().get_bool("#unwind_path"))
    return instrumentation_resultt::DID_NOTHING;

  // save the address of the next instruction
  goto_programt::targett next_it = instr_it;
  next_it++;

  const auto &function = instr_it->call_function();
  DATA_INVARIANT(
    function.id() == ID_symbol, "function call expected to be a symbol");
  const irep_idt &callee_id = to_symbol_expr(function).identifier();

  if(function_may_throw(callee_id))
  {
    const exprt no_exception_currently_in_flight = no_inflight_exception();

    if(symbol_table.lookup_ref(callee_id).type.get_bool(ID_C_must_not_throw))
    {
      // Function is annotated must-not-throw, but we can't prove that here.
      goto_program.insert_after(
        instr_it,
        goto_programt::make_assumption(no_exception_currently_in_flight));
      return instrumentation_resultt::ADDED_CODE_WITHOUT_MAY_THROW;
    }
    else
    {
      add_exception_dispatch_sequence(
        function_identifier, goto_program, instr_it, stack_catch, locals);

      // guard the dispatch with a check that an exception is in flight
      goto_program.insert_after(
        instr_it,
        goto_programt::make_goto(
          next_it,
          no_exception_currently_in_flight,
          instr_it->source_location()));
      return instrumentation_resultt::ADDED_CODE_WITH_MAY_THROW;
    }
  }

  return instrumentation_resultt::DID_NOTHING;
}

void remove_exceptions_baset::instrument_exceptions(
  const irep_idt &function_identifier,
  goto_programt &goto_program)
{
  stack_catcht stack_catch;                            // stack of try-catch
  std::vector<std::vector<symbol_exprt>> stack_locals; // stack of local vars
  std::vector<symbol_exprt> locals;

  if(goto_program.empty())
    return;

  bool program_or_callees_may_throw =
    function_or_callees_may_throw(goto_program);

  bool did_something = false;

  Forall_goto_program_instructions(instr_it, goto_program)
  {
    if(instr_it->is_decl())
    {
      locals.push_back(instr_it->decl_symbol());
    }
    else if(instr_it->type() == CATCH)
    {
      const irep_idt &statement = instr_it->code().get_statement();
      if(statement == ID_exception_landingpad)
      {
        instrument_exception_handler(
          goto_program, instr_it, program_or_callees_may_throw);
      }
      else if(statement == ID_pop_catch)
      {
        if(!stack_locals.empty())
        {
          locals = stack_locals.back();
          stack_locals.pop_back();
        }
        if(!stack_catch.empty())
          stack_catch.pop_back();
      }
      else if(statement == ID_push_catch)
      {
        stack_locals.push_back(locals);
        locals.clear();

        catch_handlerst handlers;

        const code_push_catcht::exception_listt &exception_list =
          to_code_push_catch(instr_it->code()).exception_list();

        INVARIANT(
          instr_it->targets.empty() ||
            exception_list.size() == instr_it->targets.size(),
          "`exception_list` should contain current instruction's targets");

        std::size_t i = 0;
        for(auto target : instr_it->targets)
        {
          handlers.push_back(
            std::make_pair(exception_list[i].get_tag(), target));
          i++;
        }
        stack_catch.push_back(std::move(handlers));
      }
      else
      {
        INVARIANT(
          false,
          "CATCH opcode should be one of push-catch, pop-catch, landingpad");
      }

      instr_it->turn_into_skip();
      did_something = true;
    }
    else if(instr_it->type() == THROW)
    {
      did_something = instrument_throw(
        function_identifier, goto_program, instr_it, stack_catch, locals);
    }
    else if(instr_it->type() == FUNCTION_CALL)
    {
      instrumentation_resultt result = instrument_function_call(
        function_identifier, goto_program, instr_it, stack_catch, locals);
      did_something =
        did_something || result != instrumentation_resultt::DID_NOTHING;
    }
    else if(
      instr_it->is_goto() &&
      instr_it->condition().get_bool("#cpp_unwind_guard"))
    {
      // guard of a call-site unwind cleanup: skip the cleanup when no
      // exception is in flight
      instr_it->condition_nonconst() = no_inflight_exception();
      did_something = true;
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

void remove_exceptions_baset::operator()(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    instrument_exceptions(gf_entry.first, gf_entry.second.body);
}

void remove_exceptions_baset::operator()(
  const irep_idt &function_identifier,
  goto_programt &goto_program)
{
  instrument_exceptions(function_identifier, goto_program);
}
