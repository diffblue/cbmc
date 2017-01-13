#include <algorithm>

#include <goto-programs/goto_trace.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_vector_solution.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/print_control_solution.h>
#include <cegis/control/learn/vector_solution_configuration.h>

void vector_solution_configurationt::nondeterminise_solution_configuration(
    symbol_tablet &st, goto_functionst &gf)
{
}

namespace
{
bool is_solution(const goto_trace_stept &step)
{
  const exprt &lhs=step.full_lhs;
  if (ID_symbol != lhs.id()) return false;
  const std::string &id=id2string(to_symbol_expr(lhs).get_identifier());
  return CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME == id;
}

const struct_exprt &find_solution(const goto_tracet &trace)
{
  const goto_tracet::stepst &steps=trace.steps;
  const auto it=std::find_if(steps.begin(), steps.end(), is_solution);
  assert(steps.end() != it);
  return to_struct_expr(it->full_lhs_value);
}
}

void vector_solution_configurationt::convert(solutiont &current_candidate,
    const goto_tracet &trace, const symbol_tablet &st)
{
  const namespacet ns(st);
  const struct_exprt &value=find_solution(trace);
  current_candidate.K=get_K_controller_comp(ns, value);
}

void vector_solution_configurationt::show_candidate(messaget::mstreamt &os,
    const solutiont &candidate, const symbol_tablet &st)
{
  print_control_array(os, candidate.K, "K", st);
}
