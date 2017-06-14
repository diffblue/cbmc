/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Assembler -> Goto

#include "goto_convert_class.h"

void goto_convertt::convert_asm(
  const code_asmt &code,
  goto_programt &dest)
{
  // copy as OTHER
  copy(code, OTHER, dest);
}
