/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/message.h>

#include <goto-programs/goto_inline.h>

#include <cegis/cegis-util/program_helper.h>

namespace
{
bool is_user_function(const irep_idt &name,
    const goto_functionst::goto_functiont &func)
{
  if (std::string::npos != id2string(name).find(id2string(CPROVER_PREFIX)))
    return false;
  if (!func.body_available()) return false;
  const goto_programt::instructionst &instrs=func.body.instructions;
  if (instrs.empty()) return false;
  return !is_builtin(instrs.front().source_location);
}

void mark_user_function(const irep_idt &name,
    goto_functionst::goto_functiont &func)
{
  if (is_user_function(name, func)) func.type.set_inlined(true);
}
}

void inline_user_program(const symbol_tablet &st, goto_functionst &gf)
{
  for (goto_functionst::function_mapt::value_type &f : gf.function_map)
    mark_user_function(f.first, f.second);

  const namespacet ns(st);
  null_message_handlert msg;
  goto_partial_inline(gf, ns, msg, 0);
}
