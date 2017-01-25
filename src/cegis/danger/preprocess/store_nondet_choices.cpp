/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/danger/options/danger_program.h>

namespace
{
void store_skolem_choices_for_loop(invariant_programt::invariant_loopt *loop)
{
  const danger_programt::program_ranget &range=loop->body;
  const goto_programt::targett &end=range.end;
  for (goto_programt::targett it=range.begin; it != end; ++it)
    if (is_nondet(it, end)) loop->skolem_choices.push_back(it);
}
}

void store_skolem_choices(invariant_programt &program)
{
  invariant_programt::invariant_loopst loops(program.get_loops());
  std::for_each(loops.begin(), loops.end(), &store_skolem_choices_for_loop);
}

namespace
{
void store_x0_choices_for_range(invariant_programt &program,
    const goto_programt::targett &begin, const goto_programt::targett &end)
{
  for (goto_programt::targett it=begin; it != end; ++it)
    if (is_nondet(it, end)) program.x0_choices.push_back(it);
}
}

void store_x0_choices(invariant_programt &program)
{
  goto_programt::targett begin=program.invariant_range.begin;
  goto_programt::targett end;
  const invariant_programt &prog=program;
  const invariant_programt::const_invariant_loopst loops(prog.get_loops());
  for (const invariant_programt::const_invariant_loopst::value_type &loop : loops)
  {
    end=loop->body.begin;
    store_x0_choices_for_range(program, begin, end);
    begin=loop->body.end;
  }
  end=program.invariant_range.end;
  store_x0_choices_for_range(program, begin, end);
}
