/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <functional>

#include <util/expr_util.h>
#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/symex/verify/extract_counterexample.h>

namespace
{
goto_programt::instructiont::labelst::const_iterator find_ceq_label(
    const goto_programt::const_targett &pc)
{
  const goto_programt::instructiont::labelst &l=pc->labels;
  return std::find_if(l.begin(), l.end(),
      [](const irep_idt &label)
      { return std::string::npos != id2string(label).find(DANGER_CE_QUANTIFIER_LABEL_PREFIX);});
}

bool has_label(const goto_programt::const_targett &pc, const irep_idt &id)
{
  const goto_programt::instructiont::labelst &l=pc->labels;
  return l.end() != std::find(l.begin(), l.end(), id);
}

class extract_counterexamplet
{
  counterexamplet &result;
  goto_programt::targetst q;

  bool should_extract(const goto_trace_stept &step)
  {
    const goto_programt::instructiont::labelst::const_iterator it=
        find_ceq_label(step.pc);
    if (step.pc->labels.end() == it) return false;
    const irep_idt &label=*it;
    const size_t original_size=q.size();
    q.erase(
        std::remove_if(q.begin(), q.end(),
            std::bind(has_label, std::placeholders::_1, label)), q.end());
    return q.size() != original_size;
  }
public:
  extract_counterexamplet(counterexamplet &result,
      const goto_programt::targetst &quantifiers) :
      result(result), q(quantifiers)
  {
  }

  void finalise()
  {
    for (const goto_programt::targett &pos : q)
    {
      const irep_idt &var=get_affected_variable(*pos);
      const exprt value(gen_zero(get_affected_type(*pos)));
      result.insert(std::make_pair(var, value));
    }
    q.clear();
  }

  bool is_done() const
  {
    return q.empty();
  }

  void operator()(const goto_trace_stept &step)
  {
    if (!should_extract(step)) return;
    const symbol_exprt &lhs=step.lhs_object;
    result.insert(std::make_pair(lhs.get_identifier(), step.lhs_object_value));
  }
};
}

void invariant_extract_counterexample(counterexamplet &result,
    const goto_tracet &trace, const goto_programt::targetst &quantifiers)
{
  const size_t existing_entries=result.size();
  const goto_tracet::stepst &s=trace.steps;
  extract_counterexamplet extract(result, quantifiers);
  typedef goto_tracet::stepst::const_iterator itt;
  for (itt it=s.begin(); it != s.end() && !extract.is_done(); ++it)
    extract(*it);
  extract.finalise();
  const size_t new_entries=result.size() - existing_entries;
  assert(new_entries == quantifiers.size());
  assert(extract.is_done());
}
