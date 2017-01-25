/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/refactor/options/refactor_program.h>
#include <cegis/refactor/preprocessing/collect_counterexamples.h>

namespace
{
bool is_meta(const goto_programt::const_targett target)
{
  return false;
}
}

void collect_counterexamples(refactor_programt &prog)
{
  refactor_programt::counterexample_locationst &ls=prog.counterexample_locations;
  typedef goto_functionst::function_mapt fmapt;
  size_t idx=0;
  for (fmapt::value_type &entry : prog.gf.function_map)
  {
    fmapt::value_type::second_type &func=entry.second;
    if (!func.body_available()) continue;
    goto_programt::targetst &ce_locs=ls[entry.first];
    idx=collect_counterexample_locations(ce_locs, func.body, is_meta, idx);
  }
}
