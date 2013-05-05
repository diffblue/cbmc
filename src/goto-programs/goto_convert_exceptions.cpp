/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::convert_msc_try_finally

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_try_finally(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "msc_try_finally expects two arguments";
  }
  
  goto_programt tmp;
  tmp.add_instruction(SKIP)->location=code.location();

  {  
    // save 'leave' target
    leave_targett leave_target(targets);
    targets.set_leave(tmp.instructions.begin());
  
    // first put 'finally' code onto destructor stack
    targets.destructor_stack.push_back(to_code(code.op1()));
  
    // do 'try' code
    convert(to_code(code.op0()), dest);

    // pop 'finally' from destructor stack
    targets.destructor_stack.pop_back();
    
    // 'leave' target gets restored here
  }

  // now add 'finally' code
  convert(to_code(code.op1()), dest);
  
  // this is the target for 'leave'
  dest.destructive_append(tmp);
}

/*******************************************************************\

Function: goto_convertt::convert_msc_try_except

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_try_except(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=3)
  {
    err_location(code);
    throw "msc_try_except expects three arguments";
  }

  convert(to_code(code.op0()), dest);
  
  // todo: generate exception tracking
}

/*******************************************************************\

Function: goto_convertt::convert_msc_leave

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_leave(
  const codet &code,
  goto_programt &dest)
{
  if(targets.leave_set)
  {
    err_location(code);
    throw "leave without target";
  }
  
  // need to process destructor stack
  for(unsigned d=targets.destructor_stack.size();
      d!=targets.leave_stack_size;
      d--)
  {
    codet d_code=targets.destructor_stack[d-1];
    d_code.location()=code.location();
    convert(d_code, dest);
  }

  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.leave_target);
  t->location=code.location();
}

/*******************************************************************\

Function: goto_convertt::convert_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_catch(
  const codet &code,
  goto_programt &dest)
{
  assert(code.operands().size()>=2);
  
  // add the CATCH-push instruction to 'dest'
  goto_programt::targett catch_push_instruction=dest.add_instruction();
  catch_push_instruction->make_catch();
  catch_push_instruction->code.set_statement(ID_catch);
  catch_push_instruction->location=code.location();
  
  // the CATCH-push instruction is annotated with a list of IDs,
  // one per target
  irept::subt &exception_list=
    catch_push_instruction->code.add(ID_exception_list).get_sub();

  // add a SKIP target for the end of everything
  goto_programt end;
  goto_programt::targett end_target=end.add_instruction();
  end_target->make_skip();
  
  // the first operand is the 'try' block
  convert(to_code(code.op0()), dest);
  
  // add the CATCH-pop to the end of the 'try' block
  goto_programt::targett catch_pop_instruction=dest.add_instruction();
  catch_pop_instruction->make_catch();
  catch_pop_instruction->code.set_statement(ID_catch);
  
  // add a goto to the end of the 'try' block
  dest.add_instruction()->make_goto(end_target);

  for(unsigned i=1; i<code.operands().size(); i++)
  {
    const codet &block=to_code(code.operands()[i]);
  
    // grab the ID and add to CATCH instruction
    exception_list.push_back(irept(block.get(ID_exception_id)));
    
    goto_programt tmp;
    convert(block, tmp);
    catch_push_instruction->targets.push_back(tmp.instructions.begin());
    dest.destructive_append(tmp);

    // add a goto to the end of the 'catch' block
    dest.add_instruction()->make_goto(end_target);
  }

  // add end-target  
  dest.destructive_append(end);
}

/*******************************************************************\

Function: goto_convertt::convert_CPROVER_try_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_CPROVER_try_catch(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "CPROVER_try_catch expects two arguments";
  }

  // this is where we go after 'throw'
  goto_programt tmp;
  tmp.add_instruction(SKIP)->location=code.location();

  // set 'throw' target
  throw_targett throw_target(targets);
  targets.set_throw(tmp.instructions.begin());
  
  // now put 'catch' code onto destructor stack
  code_ifthenelset catch_code;
  catch_code.cond()=exception_flag();
  catch_code.location()=code.location();
  catch_code.then_case()=code.op1();

  targets.destructor_stack.push_back(catch_code);

  // now convert 'try' code
  convert(to_code(code.op0()), dest);

  // pop 'catch' code off stack
  targets.destructor_stack.pop_back();
  
  // add 'throw' target
  dest.destructive_append(tmp);
}

/*******************************************************************\

Function: goto_convertt::convert_CPROVER_throw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_CPROVER_throw(
  const codet &code,
  goto_programt &dest)
{
  // set the 'exception' flag
  {
    goto_programt::targett t_set_exception=
      dest.add_instruction(ASSIGN);

    t_set_exception->location=code.location();
    t_set_exception->code=code_assignt(exception_flag(), true_exprt());
  }

  // do we catch locally?
  if(targets.throw_set)
  {
    // need to process destructor stack
    unwind_destructor_stack(code.location(), targets.throw_stack_size, dest);

    // add goto
    goto_programt::targett t=dest.add_instruction();
    t->make_goto(targets.throw_target);
    t->location=code.location();
  }
  else // otherwise, we do a return
  {
    // need to process destructor stack
    for(destructor_stackt::const_reverse_iterator
        d_it=targets.destructor_stack.rbegin();
        d_it!=targets.destructor_stack.rend();
        d_it++)
    {
      codet d_code=*d_it;
      d_code.location()=code.location();
      convert(d_code, dest);
    }

    goto_programt::targett t=dest.add_instruction(RETURN);
    t->location=code.location();
    t->code=code_returnt();
  }
}

/*******************************************************************\

Function: goto_convertt::convert_CPROVER_try_finally

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_CPROVER_try_finally(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "CPROVER_try_finally expects two arguments";
  }
  
  // first put 'finally' code onto destructor stack
  targets.destructor_stack.push_back(to_code(code.op1()));
  
  // do 'try' code
  convert(to_code(code.op0()), dest);

  // pop 'finally' from destructor stack
  targets.destructor_stack.pop_back();

  // now add 'finally' code
  convert(to_code(code.op1()), dest);
}

/*******************************************************************\

Function: goto_convertt::exception_flag

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt goto_convertt::exception_flag()
{
  irep_idt id="c::$exception_flag";

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
    symbol_table.move(new_symbol);
  }
  
  return symbol_exprt(id, bool_typet());
}
    
/*******************************************************************\

Function: goto_convertt::unwind_destructor_stack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::unwind_destructor_stack(
  const locationt &location,
  unsigned stack_size,
  goto_programt &dest,
  bool do_dead)
{
  // There might be exceptions happening in the exception
  // handler. We thus pop off the stack, and then later
  // one restore the original stack.
  destructor_stackt old_stack=targets.destructor_stack;

  while(targets.destructor_stack.size()>stack_size)
  {
    codet d_code=targets.destructor_stack.back();
    d_code.location()=location;
    
    // pop now to avoid doing this again
    targets.destructor_stack.pop_back();
 
    if(do_dead || d_code.get_statement()!=ID_dead)
      convert(d_code, dest);
  }

  // Now restore old stack.
  old_stack.swap(targets.destructor_stack);  
}
