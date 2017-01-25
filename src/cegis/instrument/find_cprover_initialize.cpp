/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/instrument/literals.h>
#include <cegis/instrument/find_cprover_initialize.h>

goto_programt::targett find_cprover_initialize(goto_programt &body)
{
  goto_programt::instructionst &instrs=body.instructions;
  goto_programt::targett pos;
  const goto_programt::targett end=instrs.end();
  for (pos=instrs.begin(); pos != end; ++pos)
  {
    const goto_programt::instructiont &instr=*pos;
    if (goto_program_instruction_typet::FUNCTION_CALL != instr.type) continue;
    const code_function_callt &call=to_code_function_call(instr.code);
    const exprt &func=call.function();
    if (ID_symbol != func.id()) continue;
    const std::string &func_id=id2string(to_symbol_expr(func).get_identifier());
    if (CPROVER_INIT == func_id) break;
  }
  assert(end != pos);
  return pos;
}

goto_programt::targett find_last_instr(goto_programt &body)
{
  goto_programt::targett result=body.instructions.end();
  assert(goto_program_instruction_typet::END_FUNCTION == (--result)->type);
  return --result;
}
