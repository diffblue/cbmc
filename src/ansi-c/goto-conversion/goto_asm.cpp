/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Assembler -> Goto

#include "goto_convert_class.h"

#include "destructor.h"

void goto_convertt::convert_asm(
  const code_asmt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(code.get_flavor() != ID_gcc || code.operands().size() != 5)
  {
    // copy as OTHER
    copy(code, OTHER, dest);
    return;
  }

  // The operands of a gcc-style statement are evaluated before the statement
  // executes; side effects in them (function calls, assignments, statement
  // expressions) need to be made explicit so that the lowering of the
  // statement only sees side-effect free expressions.
  code_asm_gcct new_code = to_code_asm_gcc(code);
  clean_expr_resultt side_effects;
  for(auto *list : {&new_code.outputs(), &new_code.inputs()})
  {
    for(auto &operand : list->operands())
    {
      if(operand.operands().size() != 2)
        continue;
      exprt &expr = to_binary_expr(operand).op1();
      if(needs_cleaning(expr))
        side_effects.add(clean_expr(expr, mode));
    }
  }
  dest.destructive_append(side_effects.side_effects);

  copy(new_code, OTHER, dest);

  destruct_locals(side_effects.temporaries, dest, ns);
}
