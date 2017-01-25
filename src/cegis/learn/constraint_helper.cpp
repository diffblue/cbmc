/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>

void transform_asserts_to_assumes(goto_functionst &gf)
{
  typedef goto_functionst::function_mapt fmapt;
  fmapt &fmap=gf.function_map;
  for (fmapt::value_type &entry : fmap)
  {
    if (!entry.second.body_available()) continue;
    for (goto_programt::instructiont &instr : entry.second.body.instructions)
      if (ASSERT == instr.type) instr.type=ASSUME;
  }
}
