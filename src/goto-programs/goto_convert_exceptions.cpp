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
  DATA_INVARIANT(
    code.operands().size() == 2,
    code.find_source_location().as_string() +
      ": msc_try_finally expects two arguments");

  goto_programt tmp;
  tmp.add_instruction(SKIP)->source_location=code.source_location();

  {
    // save 'leave' target
    leave_targett leave_target(targets);
    targets.set_leave(tmp.instructions.begin());

    // first put 'finally' code onto destructor stack
    targets.destructor_stack.push_back(to_code(code.op1()));

    // do 'try' code
    convert(to_code(code.op0()), dest, mode);

    // pop 'finally' from destructor stack
    targets.destructor_stack.pop_back();

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
  DATA_INVARIANT(
    code.operands().size() == 3,
    code.find_source_location().as_string() +
      ": msc_try_except expects three arguments");

  convert(to_code(code.op0()), dest, mode);

  // todo: generate exception tracking
}

void goto_convertt::convert_msc_leave(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  DATA_INVARIANT(
    targets.leave_set,
    code.find_source_location().as_string() + ": leave without target");

  // need to process destructor stack
  for(std::size_t d=targets.destructor_stack.size();
      d!=targets.leave_stack_size;
      d--)
  {
    codet d_code=targets.destructor_stack[d-1];
    d_code.add_source_location()=code.source_location();
    convert(d_code, dest, mode);
  }

  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.leave_target);
  t->source_location=code.source_location();
}

void goto_convertt::convert_try_catch(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  DATA_INVARIANT(
    code.operands().size() >= 2,
    code.find_source_location().as_string() +
      ": try_catch expects at least two arguments");

  // add the CATCH-push instruction to 'dest'
  goto_programt::targett catch_push_instruction=dest.add_instruction();
  catch_push_instruction->make_catch();
  catch_push_instruction->source_location=code.source_location();

  code_push_catcht push_catch_code;

  // the CATCH-push instruction is annotated with a list of IDs,
  // one per target
  code_push_catcht::exception_listt &exception_list=
    push_catch_code.exception_list();

  // add a SKIP target for the end of everything
  goto_programt end;
  goto_programt::targett end_target=end.add_instruction();
  end_target->make_skip();

  // the first operand is the 'try' block
  convert(to_code(code.op0()), dest, mode);

  // add the CATCH-pop to the end of the 'try' block
  goto_programt::targett catch_pop_instruction=dest.add_instruction();
  catch_pop_instruction->make_catch();
  catch_pop_instruction->code=code_pop_catcht();

  // add a goto to the end of the 'try' block
  dest.add_instruction()->make_goto(end_target);

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
    dest.add_instruction()->make_goto(end_target);
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
  DATA_INVARIANT(
    code.operands().size() == 2,
    code.find_source_location().as_string() +
      ": CPROVER_try_catch expects two arguments");

  // this is where we go after 'throw'
  goto_programt tmp;
  tmp.add_instruction(SKIP)->source_location=code.source_location();

  // set 'throw' target
  throw_targett throw_target(targets);
  targets.set_throw(tmp.instructions.begin());

  // now put 'catch' code onto destructor stack
  code_ifthenelset catch_code;
  catch_code.cond()=exception_flag();
  catch_code.add_source_location()=code.source_location();
  catch_code.then_case()=to_code(code.op1());

  targets.destructor_stack.push_back(catch_code);

  // now convert 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'catch' code off stack
  targets.destructor_stack.pop_back();

  // add 'throw' target
  dest.destructive_append(tmp);
}

void goto_convertt::convert_CPROVER_throw(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // set the 'exception' flag
  {
    goto_programt::targett t_set_exception=
      dest.add_instruction(ASSIGN);

    t_set_exception->source_location=code.source_location();
    t_set_exception->code=code_assignt(exception_flag(), true_exprt());
  }

  // do we catch locally?
  if(targets.throw_set)
  {
    // need to process destructor stack
    unwind_destructor_stack(
      code.source_location(), targets.throw_stack_size, dest, mode);

    // add goto
    goto_programt::targett t=dest.add_instruction();
    t->make_goto(targets.throw_target);
    t->source_location=code.source_location();
  }
  else // otherwise, we do a return
  {
    // need to process destructor stack
    unwind_destructor_stack(code.source_location(), 0, dest, mode);

    // add goto
    goto_programt::targett t=dest.add_instruction();
    t->make_goto(targets.return_target);
    t->source_location=code.source_location();
  }
}

void goto_convertt::convert_CPROVER_try_finally(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  DATA_INVARIANT(
    code.operands().size() == 2,
    code.find_source_location().as_string() +
      ": CPROVER_try_finally expects two arguments");

  // first put 'finally' code onto destructor stack
  targets.destructor_stack.push_back(to_code(code.op1()));

  // do 'try' code
  convert(to_code(code.op0()), dest, mode);

  // pop 'finally' from destructor stack
  targets.destructor_stack.pop_back();

  // now add 'finally' code
  convert(to_code(code.op1()), dest, mode);
}

symbol_exprt goto_convertt::exception_flag()
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
    symbol_table.insert(std::move(new_symbol));
  }

  return symbol_exprt(id, bool_typet());
}

void goto_convertt::unwind_destructor_stack(
  const source_locationt &source_location,
  std::size_t final_stack_size,
  goto_programt &dest,
  const irep_idt &mode)
{
  unwind_destructor_stack(
    source_location, final_stack_size, dest, targets.destructor_stack, mode);
}

void goto_convertt::unwind_destructor_stack(
  const source_locationt &source_location,
  std::size_t final_stack_size,
  goto_programt &dest,
  destructor_stackt &destructor_stack,
  const irep_idt &mode)
{
  // There might be exceptions happening in the exception
  // handler. We thus pop off the stack, and then later
  // one restore the original stack.
  destructor_stackt old_stack=destructor_stack;

  while(destructor_stack.size()>final_stack_size)
  {
    codet d_code=destructor_stack.back();
    d_code.add_source_location()=source_location;

    // pop now to avoid doing this again
    destructor_stack.pop_back();

    convert(d_code, dest, mode);
  }

  // Now restore old stack.
  old_stack.swap(destructor_stack);
}
