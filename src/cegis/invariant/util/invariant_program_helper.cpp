/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/wordsize/restrict_bv_size.h>
#include <cegis/invariant/options/invariant_program.h>

void erase_target(goto_programt::instructionst &body,
    const goto_programt::targett &target)
{
  goto_programt::targett succ=std::next(target);
  assert(succ != body.end());

  for(goto_programt::instructiont &instr : body)
    for(goto_programt::targett &t : instr.targets)
      if(target == t) t=succ;

  body.erase(target);
}

void restrict_bv_size(invariant_programt &prog, const size_t width_in_bits)
{
  restrict_bv_size(prog.st, prog.gf, width_in_bits);
  const invariant_programt::invariant_loopst loops(prog.get_loops());
  for(invariant_programt::invariant_loopt * const loop : loops)
    restrict_bv_size(loop->guard, width_in_bits);
  restrict_bv_size(prog.assertion, width_in_bits);
}
