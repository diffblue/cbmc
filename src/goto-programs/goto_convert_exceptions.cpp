/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <cassert>

#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/rename.h>

#include <ansi-c/c_types.h>

#include "goto_convert.h"
#endif
#include "goto_convert_class.h"

//#include "destructor.h"

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

  convert(to_code(code.op0()), dest);
  
  // todo: generate exception tracking
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
  // todo: should throw (silent) exception
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
  // this gets compiled into a goto, much like break and continue
  
}
