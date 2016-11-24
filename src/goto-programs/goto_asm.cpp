/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::convert_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_asm(
  const code_asmt &code,
  goto_programt &dest)
{
  // copy as OTHER
  copy(code, OTHER, dest);  
}
