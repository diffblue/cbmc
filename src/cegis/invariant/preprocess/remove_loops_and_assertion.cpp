/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/simplify_expr.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/preprocess/remove_loops_and_assertion.h>

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

goto_programt::targett handle_loop_removal(invariant_programt &program,
    goto_programt::instructionst &instrs, goto_programt::targett target)
{
  if (!target->is_backwards_goto()) return target;
  invariant_programt::invariant_loopt &loop=program.add_loop();
  const goto_programt::targett next_in_loop=std::prev(target);
  invariant_remove_loop(program.st, instrs, target, loop.guard, loop.body.begin,
      loop.body.end);
  return next_in_loop;
}
}

void invariant_remove_loop(const symbol_tablet &st,
    goto_programt::instructionst &instrs, const goto_programt::targett &target,
    exprt &guard, goto_programt::targett &body_begin,
    goto_programt::targett &body_end)
{
  const goto_programt::instructiont &instr=*target;
  const namespacet ns(st);
  const goto_programt::targett goto_target=instr.get_target();
  if (instr.guard.is_true())
  {
    goto_programt::targett guard_instr=goto_target;
    const goto_programt::targett end=instrs.end();
    while (end != guard_instr && guard_instr->guard.is_true())
      ++guard_instr;
    assert(end != guard_instr);
    if (ID_not == guard.id()) guard=to_not_expr(guard_instr->guard).op();
    else guard=simplify_expr(not_exprt(guard_instr->guard), ns);
    body_begin=std::next(guard_instr);
    erase_target(instrs, guard_instr);
  } else
  {
    guard=simplify_expr(instr.guard, ns);
    body_begin=goto_target;
  }
  assert(!guard.id().empty());
  body_end=std::prev(target);
  erase_target(instrs, target);
  ++body_end;
}

void invariant_remove_loops_and_assertion(invariant_programt &program)
{
  goto_programt &body=get_entry_body(program.gf);
  goto_programt::instructionst &instrs=body.instructions;
  program.invariant_range.begin=instrs.begin();
  for (goto_programt::targett it=instrs.begin(); it != instrs.end(); ++it)
  {
    if (handle_assertion_removal(program, instrs, it)) break;
    it=handle_loop_removal(program, instrs, it);
  }
}
