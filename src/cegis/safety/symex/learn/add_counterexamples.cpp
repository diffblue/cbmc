/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/constraint/safety_constraint_factory.h>
#include <cegis/safety/symex/learn/add_counterexamples.h>

namespace
{
void positional_assign(invariant_programt &prog,
    const goto_programt::targetst &vars, const counterexamplest &values,
    const std::string &pre)
{
  const counterexamplet &ce_template=values.front();
  for (const goto_programt::targett x0 : vars)
  {
    const irep_idt &id=get_affected_variable(*x0);
    const counterexamplet::const_iterator it=ce_template.find(id);
    assert(ce_template.end() != it);
    counterexamplet tmp;
    tmp.insert(std::make_pair(id, it->second));
    invariant_assign_ce_values(prog, tmp, values.size(), pre, x0, false);
  }
}
}

void safety_add_learned_counterexamples(safety_programt &prog,
    const safety_goto_cest &ces, constraint_factoryt constraint)
{
  if (ces.empty()) return;
  // TODO: Implement for multiple loops (change constraint, instrumentation)
  counterexamplest x0s;
  std::transform(ces.begin(), ces.end(), std::back_inserter(x0s),
      [](const safety_goto_cet &ce)
      { return ce.x0;});
  counterexamplest first_loop_only;
  std::transform(ces.begin(), ces.end(), std::back_inserter(first_loop_only),
      [](const safety_goto_cet &ce)
      { assert(!ce.x.empty()); return ce.x.front();});
  const std::string x0_pre(X0_CHOICE_PREFIX);
  const std::string x_pre(X_CHOICE_PREFIX);
  invariant_declare_x_choice_arrays(prog, x0s, x0_pre);
  invariant_declare_x_choice_arrays(prog, first_loop_only, x_pre);
  const size_t sz=ces.size();
  const goto_programt::targett loop_end=invariant_add_ce_loop(prog, sz, false);
  positional_assign(prog, prog.x0_choices, first_loop_only, x0_pre);
  for (const goto_programt::targett x0 : prog.x0_choices)
  {
    const irep_idt &id=get_affected_variable(*x0);
    const counterexamplet &ce_template=x0s.front();
    const counterexamplet::const_iterator it=ce_template.find(id);
    assert(ce_template.end() != it);
    counterexamplet tmp;
    tmp.insert(std::make_pair(id, it->second));
    invariant_assign_ce_values(prog, tmp, x0s.size(), x0_pre, x0, false);
  }
  goto_programt::targett pos=prog.get_loops().front()->meta_variables.Ix;
  const size_t first_loop_sz=first_loop_only.size();
  invariant_assign_ce_values(prog, first_loop_only.front(), first_loop_sz,
      x_pre, pos, false);
  invariant_add_constraint(prog, constraint, loop_end);
}
