/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/goto_program.h>

void convert_instruction(goto_programt::instructiont &instruction)
{
  auto statement = instruction.code.get_statement();
  if(statement == "goto" || statement == "return")
  {
    instruction.type = GOTO;
    instruction.code.clear();
    instruction.guard = true_exprt();
  }
}

void convert_instructions(goto_programt &dest)
{
  for(auto &instruction : dest.instructions)
  {
    convert_instruction(instruction);
  }
}
