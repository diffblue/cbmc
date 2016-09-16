#include <cegis/cegis-util/program_helper.h>

void transform_asserts_to_assumes(goto_functionst &gf)
{
  goto_programt &body=get_entry_body(gf);
  for (goto_programt::instructiont &instr : body.instructions)
    if (goto_program_instruction_typet::ASSERT == instr.type)
      instr.type=goto_program_instruction_typet::ASSUME;
}
