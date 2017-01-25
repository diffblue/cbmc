/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <functional>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/preprocess/remove_loops_and_assertion.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/preprocessing/remove_loop.h>

void remove_loop(jsa_programt &p)
{
  goto_programt::instructionst &b=get_entry_body(p.gf).instructions;
  auto pred=std::mem_fn(&goto_programt::instructiont::is_backwards_goto);
  const goto_programt::targett bw_goto=std::find_if(b.begin(), b.end(), pred);
  assert(b.end() != bw_goto);
  assert(b.end() == std::find_if(std::next(bw_goto), b.end(), pred));
  goto_programt::targett body_begin;
  goto_programt::targett body_end;
  invariant_remove_loop(p.st, b, bw_goto, p.guard, p.body.first, p.body.second);
}
