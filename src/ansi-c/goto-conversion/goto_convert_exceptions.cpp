/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <goto-programs/remove_exceptions_base.h>

#include <algorithm>

void goto_convertt::convert_msc_try_finally(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 2,
    "msc_try_finally expects two arguments",
    code.find_source_location());

  goto_programt tmp;
  tmp.add(goto_programt::make_skip(code.source_location()));

  {
    // save 'leave' target
    leave_targett leave_target(targets);
    targets.set_leave(tmp.instructions.begin());

    // first put 'finally' code onto destructor stack
    node_indext old_stack_top = targets.scope_stack.get_current_node();
    targets.scope_stack.add(to_code(code.op1()), {});

    // do 'try' code
    convert(to_code(code.op0()), dest, mode);

    // pop 'finally' from destructor stack
    targets.scope_stack.set_current_node(old_stack_top);

    // 'leave' target gets restored here
  }

  // now add 'finally' code
  convert(to_code(code.op1()), dest, mode);

  // this is the target for 'leave'
  dest.destructive_append(tmp);
}

void goto_convertt::convert_msc_try_except(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 3,
    "msc_try_except expects three arguments",
    code.find_source_location());

  convert(to_code(code.op0()), dest, mode);

  // todo: generate exception tracking
}

void goto_convertt::convert_msc_leave(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    targets.leave_set, "leave without target", code.find_source_location());

  // need to process destructor stack
  unwind_destructor_stack(
    code.source_location(), dest, mode, targets.leave_stack_node);

  dest.add(
    goto_programt::make_goto(targets.leave_target, code.source_location()));
}

void goto_convertt::convert_try_catch(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() >= 2,
    "try_catch expects at least two arguments",
    code.find_source_location());

  // add the CATCH-push instruction to 'dest'
  goto_programt::targett catch_push_instruction =
    dest.add(goto_programt::make_catch(code.source_location()));

  code_push_catcht push_catch_code;

  // the CATCH-push instruction is annotated with a list of IDs,
  // one per target
  code_push_catcht::exception_listt &exception_list =
    push_catch_code.exception_list();

  // add a SKIP target for the end of everything
  goto_programt end;
  goto_programt::targett end_target = end.add(goto_programt::make_skip());

  // Exceptional-exit landing: taken when the in-flight exception matches none
  // of this try's handlers.  It runs the destructors of the automatic objects
  // in the scopes between this try and the enclosing one ([except.ctor]: every
  // object whose scope is exited during unwinding is destroyed), then
  // re-dispatches at the enclosing level via a propagate-marker THROW.
  goto_programt exceptional_exit;
  goto_programt::targett exceptional_exit_target =
    exceptional_exit.add(goto_programt::make_skip(code.source_location()));

  // Record the scope-tree node at entry to the try block, so that a `throw`
  // in the try body unwinds (runs destructors of) the automatic objects
  // constructed since entering the try before control reaches a handler
  // ([except.ctor], [except.throw]/4).
  const node_indext try_scope_node = targets.scope_stack.get_current_node();
  targets.cpp_try_scope_nodes.push_back(try_scope_node);

  // the first operand is the 'try' block
  convert(to_code(code.op0()), dest, mode);

  targets.cpp_try_scope_nodes.pop_back();

  // add the CATCH-pop to the end of the 'try' block
  goto_programt::targett catch_pop_instruction =
    dest.add(goto_programt::make_catch());
  catch_pop_instruction->code_nonconst() = code_pop_catcht();

  // add a goto to the end of the 'try' block
  dest.add(goto_programt::make_goto(end_target));

  for(std::size_t i = 1; i < code.operands().size(); i++)
  {
    const codet &block = to_code(code.operands()[i]);

    // grab the ID and add to CATCH instruction
    exception_list.push_back(
      code_push_catcht::exception_list_entryt(block.get(ID_exception_id)));

    goto_programt tmp;
    convert(block, tmp, mode);
    catch_push_instruction->targets.push_back(tmp.instructions.begin());
    dest.destructive_append(tmp);

    // add a goto to the end of the 'catch' block
    dest.add(goto_programt::make_goto(end_target));
  }

  // register the exceptional-exit landing as a pseudo-handler entry, so the
  // exception lowering can route an unmatched exception to it
  exception_list.push_back(
    code_push_catcht::exception_list_entryt(EXCEPTIONAL_EXIT_TAG));
  catch_push_instruction->targets.push_back(exceptional_exit_target);

  catch_push_instruction->code_nonconst() = push_catch_code;

  // fill the exceptional-exit landing: unwind the scopes between this try and
  // the enclosing one (nothing when they coincide), then propagate
  const node_indext enclosing_node = targets.cpp_try_scope_nodes.empty()
                                       ? node_indext{0}
                                       : targets.cpp_try_scope_nodes.back();
  emit_exceptional_unwind(
    code.source_location(),
    exceptional_exit,
    mode,
    enclosing_node,
    try_scope_node);

  // propagate-marker THROW: the exception lowering replaces this by a dispatch
  // at the enclosing level, leaving the in-flight exception untouched
  side_effect_expr_throwt propagate_expr{
    irept{}, typet{}, code.source_location()};
  propagate_expr.set("#exception_propagate", true);
  codet propagate_code = code_expressiont(std::move(propagate_expr));
  propagate_code.add_source_location() = code.source_location();
  exceptional_exit.add(goto_programt::instructiont(
    std::move(propagate_code), code.source_location(), THROW, nil_exprt(), {}));

  // normal control flow (try-body fall-through and handler completion) jumps
  // to end_target and never enters the exceptional-exit landing
  dest.destructive_append(exceptional_exit);

  // add the end-target
  dest.destructive_append(end);
}

void goto_convertt::emit_cpp_call_unwind_cleanup(
  goto_programt &dest,
  const irep_idt &mode)
{
  // No language-mode gate: only the C++ front-end registers destructors in
  // the scope tree, so the destructor-call check below already confines this
  // to C++ (and the function symbol mode is not reliably ID_cpp here).
  if(suppress_cpp_unwind_cleanup)
    return;

  if(dest.instructions.empty() || !dest.instructions.back().is_function_call())
    return;

  goto_programt::targett call_instruction = std::prev(dest.instructions.end());

  // no cleanup for CPROVER builtins and internals -- they do not throw
  const exprt &function = call_instruction->call_function();
  if(
    function.id() == ID_symbol &&
    has_prefix(
      id2string(to_symbol_expr(function).get_identifier()), CPROVER_PREFIX))
  {
    return;
  }

  // While an object's construction is pending, unwind from the node before
  // its registration so the not-yet-constructed object is not destroyed
  // ([except.ctor]/2).  The pending object's own constructor call closes the
  // window: once that call returns normally the object is fully constructed
  // (and if it throws, this cleanup -- emitted with the window still open --
  // correctly excludes it).
  std::optional<node_indext> start_node;
  if(pending_construction_start.has_value())
  {
    start_node = pending_construction_start;

    const auto &arguments = call_instruction->call_arguments();
    if(
      !arguments.empty() && arguments.front().id() == ID_address_of &&
      to_address_of_expr(arguments.front()).object().id() == ID_symbol &&
      to_symbol_expr(to_address_of_expr(arguments.front()).object())
          .get_identifier() == pending_construction_symbol)
    {
      pending_construction_start.reset();
    }
  }

  // the automatic objects between the call's scope and the innermost enclosing
  // try block (or the function base, [except.ctor]); nothing to do if none
  // needs *destruction* -- the scope tree also holds plain DEAD markers for
  // destructor-less locals, which do not warrant a cleanup
  const node_indext end_node = targets.cpp_try_scope_nodes.empty()
                                 ? node_indext{0}
                                 : targets.cpp_try_scope_nodes.back();
  const auto pending_destructors =
    targets.scope_stack.get_destructors(end_node, start_node);
  const bool have_destructor_call = std::any_of(
    pending_destructors.begin(),
    pending_destructors.end(),
    [](const destructor_and_idt &entry)
    { return entry.destructor.get_statement() == ID_function_call; });
  if(!have_destructor_call)
    return;

  const source_locationt loc = call_instruction->source_location();

  // guard: initially `true` (always skip the cleanup); the exception-lowering
  // pass rewrites it to "no exception in flight".  If the pass never runs, the
  // cleanup stays unreachable, which is the correct no-exceptions behaviour.
  exprt guard = true_exprt{};
  guard.set("#cpp_unwind_guard", true);

  goto_programt cleanup;
  goto_programt::targett cont = cleanup.add(goto_programt::make_skip(loc));

  dest.add(goto_programt::make_goto(cont, std::move(guard), loc));

  // destructor calls themselves get no nested cleanup: unwind_destructor_stack
  // sets suppress_cpp_unwind_cleanup while converting them.  It restores the
  // scope-tree current node to the *start* of the walk, which is not the true
  // current node when start_node overrides it -- save and restore explicitly
  // so later registrations attach to the right place.
  const node_indext saved_current = targets.scope_stack.get_current_node();
  emit_exceptional_unwind(loc, dest, mode, end_node, start_node);
  targets.scope_stack.set_current_node(saved_current);

  // propagate-marker THROW: the exception lowering replaces this by a dispatch
  // at the innermost try level, leaving the in-flight exception untouched
  side_effect_expr_throwt propagate_expr{irept{}, typet{}, loc};
  propagate_expr.set("#exception_propagate", true);
  codet propagate_code = code_expressiont(std::move(propagate_expr));
  propagate_code.add_source_location() = loc;
  dest.add(goto_programt::instructiont(
    std::move(propagate_code), loc, THROW, nil_exprt(), {}));

  dest.destructive_append(cleanup);

  // mark the call so the exception lowering does not add its own dispatch
  // (which would jump to a handler before the destructors above have run)
  call_instruction->code_nonconst().set("#cpp_unwind_cleanup_follows", true);
}

/// Emit destructor calls for an *exceptional* unwind path (an exception is in
/// flight) into \p dest and mark them "#unwind_path": the exception lowering
/// must not add its in-flight dispatch after them, which would jump to a
/// handler mid-unwind and skip the remaining destructors.  A destructor that
/// throws during unwinding terminates anyway ([except.terminate]); destructor
/// calls on *normal* scope exits keep their dispatch, so an exception from
/// them still propagates ([except.ctor]).
void goto_convertt::emit_exceptional_unwind(
  const source_locationt &source_location,
  goto_programt &dest,
  const irep_idt &mode,
  std::optional<node_indext> end_node,
  std::optional<node_indext> start_node)
{
  goto_programt unwind;
  unwind_destructor_stack(source_location, unwind, mode, end_node, start_node);

  for(auto &instruction : unwind.instructions)
  {
    if(instruction.is_function_call())
      instruction.code_nonconst().set("#unwind_path", true);
  }

  dest.destructive_append(unwind);
}

void goto_convertt::convert_CPROVER_try_catch(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 2,
    "CPROVER_try_catch expects two arguments",
    code.find_source_location());

  // this is where we go after 'throw'
  goto_programt tmp;
  tmp.add(goto_programt::make_skip(code.source_location()));

  // set 'throw' target
  throw_targett throw_target(targets);
  targets.set_throw(tmp.instructions.begin());

  // now put 'catch' code onto destructor stack
  code_ifthenelset catch_code(exception_flag(mode), to_code(code.op1()));
  catch_code.add_source_location() = code.source_location();

  // Store the point before the temp catch code.
  node_indext old_stack_top = targets.scope_stack.get_current_node();
  targets.scope_stack.add(catch_code, {});

  // now convert 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'catch' code off stack
  targets.scope_stack.set_current_node(old_stack_top);

  // add 'throw' target
  dest.destructive_append(tmp);
}

void goto_convertt::convert_CPROVER_throw(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // set the 'exception' flag
  dest.add(goto_programt::make_assignment(
    exception_flag(mode), true_exprt(), code.source_location()));

  // do we catch locally?
  if(targets.throw_set)
  {
    // need to process destructor stack
    unwind_destructor_stack(
      code.source_location(), dest, mode, targets.throw_stack_node);

    // add goto
    dest.add(
      goto_programt::make_goto(targets.throw_target, code.source_location()));
  }
  else // otherwise, we do a return
  {
    // need to process destructor stack
    unwind_destructor_stack(code.source_location(), dest, mode);

    // add goto
    dest.add(
      goto_programt::make_goto(targets.return_target, code.source_location()));
  }
}

void goto_convertt::convert_CPROVER_try_finally(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 2,
    "CPROVER_try_finally expects two arguments",
    code.find_source_location());

  // first put 'finally' code onto destructor stack
  node_indext old_stack_top = targets.scope_stack.get_current_node();
  targets.scope_stack.add(to_code(code.op1()), {});

  // do 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'finally' from destructor stack
  targets.scope_stack.set_current_node(old_stack_top);

  // now add 'finally' code
  convert(to_code(code.op1()), dest, mode);
}

symbol_exprt goto_convertt::exception_flag(const irep_idt &mode)
{
  irep_idt id = "$exception_flag";

  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(id);

  if(s_it == symbol_table.symbols.end())
  {
    symbolt new_symbol{id, bool_typet{}, mode};
    new_symbol.base_name = "$exception_flag";
    new_symbol.is_lvalue = true;
    new_symbol.is_thread_local = true;
    symbol_table.insert(std::move(new_symbol));
  }

  return symbol_exprt(id, bool_typet());
}

/// Unwinds the destructor stack and creates destructors for each node between
/// destructor_start_point and destructor_end_point (including the start,
/// excluding the end).
///
/// If \p end_index isn't passed, it will unwind the whole stack.
/// If \p start_index isn't passed, it will unwind from the current node.
///
/// When destructors are non-trivial (i.e. if they contain DECL or GOTO
/// statements) then unwinding becomes more complicated because when we call
/// convert on the destructor code it may recursively invoke this function.
///
/// Say we have a tree of [3, 2, 1, 0] and we start unwinding from top to
/// bottom. If node 1 has such a non-trivial destructor during the convert it
/// will add nodes to the tree so it ends up looking like this:
///
///     3, 2, 1, 0
///        5, 4,/
///
/// If for example the destructor contained a THROW statement then it would
/// unwind destroying variables 5, 4 and finally 0. Note that we don't have 1
/// here even if that was the instruction that triggered the recursive unwind
/// because it's already been popped off before convert is called.
///
/// After our unwind has finished, we return to our [3, 2, 1, 0] branch and
/// continue processing the branch for destructor 0.
void goto_convertt::unwind_destructor_stack(
  const source_locationt &source_location,
  goto_programt &dest,
  const irep_idt &mode,
  std::optional<node_indext> end_index,
  std::optional<node_indext> starting_index)
{
  // As we go we'll keep targets.scope_stack.current_node pointing at the
  // next node we intend to destroy, so that if our convert(...) call for each
  // destructor returns, throws or otherwise unwinds then it will carry on from
  // the correct point in the stack of variables we intend to destroy, and if it
  // contains any DECL statements they will be added as a new child branch,
  // again at the right point.

  // We back up the current node as of entering this function so this
  // side-effect is only noticed by that convert(...) call.

  node_indext start_id =
    starting_index.value_or(targets.scope_stack.get_current_node());

  targets.scope_stack.set_current_node(start_id);

  node_indext end_id = end_index.value_or(0);

  // Destructor calls emitted here get no call-site unwind cleanup of their
  // own: destructors are implicitly noexcept in C++ ([class.dtor]), and a
  // throwing destructor during unwinding terminates ([except.terminate]).
  const bool saved_suppress = suppress_cpp_unwind_cleanup;
  suppress_cpp_unwind_cleanup = true;

  while(targets.scope_stack.get_current_node() > end_id)
  {
    node_indext current_node = targets.scope_stack.get_current_node();

    std::optional<codet> &destructor =
      targets.scope_stack.get_destructor(current_node);

    // Descend the tree before unwinding so we don't re-do the current node
    // in event that convert(...) recurses into this function:
    targets.scope_stack.descend_tree();
    if(destructor)
    {
      // Copy, assign source location then convert.
      codet copied_instruction = *destructor;
      copied_instruction.add_source_location() = source_location;
      convert(copied_instruction, dest, mode);
    }
  }

  // Restore the working destructor stack to how it was before we began:
  targets.scope_stack.set_current_node(start_id);

  suppress_cpp_unwind_cleanup = saved_suppress;
}
