/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/std_expr.h>

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
    node_indext old_stack_top = targets.destructor_stack.get_current_node();
    targets.destructor_stack.add(to_code(code.op1()));

    // do 'try' code
    convert(to_code(code.op0()), dest, mode);

    // pop 'finally' from destructor stack
    targets.destructor_stack.set_current_node(old_stack_top);

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
  code_push_catcht::exception_listt &exception_list=
    push_catch_code.exception_list();

  // add a SKIP target for the end of everything
  goto_programt end;
  goto_programt::targett end_target = end.add(goto_programt::make_skip());

  // the first operand is the 'try' block
  convert(to_code(code.op0()), dest, mode);

  // add the CATCH-pop to the end of the 'try' block
  goto_programt::targett catch_pop_instruction =
    dest.add(goto_programt::make_catch());
  catch_pop_instruction->code = code_pop_catcht();

  // add a goto to the end of the 'try' block
  dest.add(goto_programt::make_goto(end_target));

  for(std::size_t i=1; i<code.operands().size(); i++)
  {
    const codet &block=to_code(code.operands()[i]);

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

  catch_push_instruction->code=push_catch_code;

  // add the end-target
  dest.destructive_append(end);
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
  catch_code.add_source_location()=code.source_location();

  // Store the point before the temp catch code.
  node_indext old_stack_top = targets.destructor_stack.get_current_node();
  targets.destructor_stack.add(catch_code);

  // now convert 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'catch' code off stack
  targets.destructor_stack.set_current_node(old_stack_top);

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
  node_indext old_stack_top = targets.destructor_stack.get_current_node();
  targets.destructor_stack.add(to_code(code.op1()));

  // do 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'finally' from destructor stack
  targets.destructor_stack.set_current_node(old_stack_top);

  // now add 'finally' code
  convert(to_code(code.op1()), dest, mode);
}

symbol_exprt goto_convertt::exception_flag(const irep_idt &mode)
{
  irep_idt id="$exception_flag";

  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(id);

  if(s_it==symbol_table.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.base_name="$exception_flag";
    new_symbol.name=id;
    new_symbol.is_lvalue=true;
    new_symbol.is_thread_local=true;
    new_symbol.is_file_local=false;
    new_symbol.type=bool_typet();
    new_symbol.mode = mode;
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
  optionalt<node_indext> end_index,
  optionalt<node_indext> starting_index)
{
  // As we go we'll keep targets.destructor_stack.current_node pointing at the
  // next node we intend to destroy, so that if our convert(...) call for each
  // destructor returns, throws or otherwise unwinds then it will carry on from
  // the correct point in the stack of variables we intend to destroy, and if it
  // contains any DECL statements they will be added as a new child branch,
  // again at the right point.

  // We back up the current node as of entering this function so this
  // side-effect is only noticed by that convert(...) call.

  node_indext start_id =
    starting_index.value_or(targets.destructor_stack.get_current_node());

  targets.destructor_stack.set_current_node(start_id);

  node_indext end_id = end_index.value_or(0);

  while(targets.destructor_stack.get_current_node() > end_id)
  {
    node_indext current_node = targets.destructor_stack.get_current_node();

    optionalt<codet> &destructor =
      targets.destructor_stack.get_destructor(current_node);

    // Descend the tree before unwinding so we don't re-do the current node
    // in event that convert(...) recurses into this function:
    targets.destructor_stack.descend_tree();
    if(destructor)
    {
      // Copy, assign source location then convert.
      codet copied_instruction = *destructor;
      copied_instruction.add_source_location() = source_location;
      convert(copied_instruction, dest, mode);
    }
  }

  // Restore the working destructor stack to how it was before we began:
  targets.destructor_stack.set_current_node(start_id);
}
