#include <util/simplify_expr.h>

#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_program_helper.h>

namespace
{
bool handle_assertion_removal(invariant_programt &program,
    goto_programt::instructionst &instrs, const goto_programt::targett &target)
{
  const goto_programt::instructiont &instr=*target;
  if (goto_program_instruction_typet::ASSERT != instr.type) return false;
  const namespacet ns(program.st);
  assert(program.assertion.id().empty());
  program.assertion=instr.guard;
  goto_programt::targett &end=program.invariant_range.end;
  end=target;
  --end;
  goto_programt::targett &last_loop_end=program.get_loops().back()->body.end;
  const bool is_last_loop_end=last_loop_end == target;
  erase_target(instrs, target);
  ++end;
  if (is_last_loop_end) last_loop_end=end;
  return true;
}

void handle_loop_removal(invariant_programt &program,
    goto_programt::instructionst &instrs, goto_programt::targett &target)
{
  const goto_programt::instructiont &instr=*target;
  if (!instr.is_backwards_goto()) return;
  const namespacet ns(program.st);
  const goto_programt::targett goto_target=instr.get_target();
  invariant_programt::invariant_loopt &loop=program.add_loop();
  if (instr.guard.is_true())
  {
    exprt guard=goto_target->guard;
    if (ID_not == guard.id()) loop.guard=to_not_expr(guard).op();
    else loop.guard=simplify_expr(not_exprt(guard), ns);
    loop.body.begin=goto_target;
    ++loop.body.begin;
    erase_target(instrs, goto_target);
  } else
  {
    loop.guard=simplify_expr(instr.guard, ns);
    loop.body.begin=goto_target;
  }
  assert(!loop.guard.id().empty());
  loop.body.end=target;
  --loop.body.end;
  erase_target(instrs, target--);
  ++loop.body.end;
}
}

void invariant_remove_loops_and_assertion(invariant_programt &program)
{
  goto_programt &body=get_entry_body(program.gf);
  goto_programt::instructionst &instrs=body.instructions;
  program.invariant_range.begin=instrs.begin();
  for (goto_programt::targett it=instrs.begin(); it != instrs.end(); ++it)
  {
    if (handle_assertion_removal(program, instrs, it)) break;
    handle_loop_removal(program, instrs, it);
  }
}
