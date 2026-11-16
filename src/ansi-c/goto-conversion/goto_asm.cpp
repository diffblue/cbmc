/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Assembler -> Goto

#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/symbol.h>

#include "destructor.h"

#include <optional>

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

  // asm goto: the translation of the statement (see remove_asm) records the
  // label it jumps to in a variable, which is dispatched on below
  std::vector<irep_idt> labels;
  for(const auto &label : new_code.labels().operands())
    labels.push_back(label.get(ID_identifier));

  std::optional<symbol_exprt> goto_target;
  if(!labels.empty())
  {
    goto_target = new_tmp_symbol(
                    unsigned_int_type(),
                    "asm_goto_target",
                    dest,
                    code.source_location(),
                    mode)
                    .symbol_expr();
    new_code.add_goto_target(*goto_target);
  }

  copy(new_code, OTHER, dest);

  // the operands are no longer needed once the statement has executed
  destruct_locals(side_effects.temporaries, dest, ns);

  if(!goto_target.has_value())
    return;

  // Jump to the label with the (1-based) index the statement chose, if any.
  // These are ordinary gotos, converted as such so that leaving scopes is
  // handled like for any other goto.
  code_deadt dead{*goto_target};
  dead.add_source_location() = code.source_location();
  for(std::size_t i = 0; i < labels.size(); ++i)
  {
    code_gotot code_goto{labels[i]};
    code_goto.add_source_location() = code.source_location();

    code_blockt then_case{{dead, std::move(code_goto)}};
    then_case.add_source_location() = code.source_location();

    code_ifthenelset if_goto{
      equal_exprt{*goto_target, from_integer(i + 1, goto_target->type())},
      std::move(then_case)};
    if_goto.add_source_location() = code.source_location();

    convert(if_goto, dest, mode);
  }

  dest.add(goto_programt::make_dead(*goto_target, code.source_location()));
}
