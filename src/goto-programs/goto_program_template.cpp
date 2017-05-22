/*******************************************************************\

Module: Goto Program Template

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "goto_program_template.h"

/*******************************************************************\

Function: operator<<

  Inputs:
    `os`: an output stream
    `t`: the instruction type to write to the stream

 Outputs: a reference to the stream which was passed in

 Purpose: prints a representation of the instruction type to the stream

\*******************************************************************/

std::ostream &operator<<(std::ostream &os, goto_program_instruction_typet t)
{
  switch(t)
  {
#define GOTO_PROG_INSTR(instr)                                                 \
  case instr:                                                                  \
    return os << #instr;
#include "goto_program_instructions.def"
  default:
    return os << '?';
  }
}
