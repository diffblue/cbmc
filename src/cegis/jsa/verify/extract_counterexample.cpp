#include <algorithm>

#include <util/expr_util.h>
#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/verify/extract_counterexample.h>

// XXX: Debug
#include <iostream>
// XXX: Debug

namespace
{
const typet &get_type(const symbol_tablet &st,
    const goto_programt::targett &pos)
{
  return st.lookup(get_affected_variable(*pos)).type;
}
}

void extract(const jsa_programt &prog, jsa_counterexamplet &ce,
    const goto_tracet &trace)
{
  const symbol_tablet &st=prog.st;
  const namespacet ns(st);
  const goto_programt::targetst &ce_locs=prog.counterexample_locations;
  const goto_tracet::stepst &steps=trace.steps;
  for (const goto_programt::targett &ce_loc : ce_locs)
  {
    assert(ce_loc->labels.size() == 1u);
    const irep_idt &id=ce_loc->labels.front();
    std::cout << "<id>" << id << "</id>" << std::endl;
    const goto_tracet::stepst::const_iterator it=std::find_if(steps.begin(),
        steps.end(), [&id](const goto_trace_stept &step)
        {
          const goto_programt::instructiont::labelst &labels=step.pc->labels;
          return labels.end() != std::find(labels.begin(), labels.end(), id);
        });
    if (steps.end() != it) ce.insert(std::make_pair(id, it->full_lhs_value));
    else
    assert(
        !"We need counterexample for each location."
            "Synthesiser can't differentiate base case/inductive step/entailment violation");
  }
  assert(ce.size() == prog.counterexample_locations.size());
}
