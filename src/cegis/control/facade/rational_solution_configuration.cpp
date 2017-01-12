#include <goto-programs/goto_trace.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/learn/nondet_solution.h>
#include <cegis/control/facade/rational_solution_configuration.h>

void nondeterminise_solution_configuration(symbol_tablet &st,
    goto_functionst &gf)
{
  nondet_control_solution(st, gf);
}

namespace
{
const struct_exprt &find_solution(const goto_tracet &trace)
{
  for (const goto_trace_stept &step : trace.steps)
  {
    const exprt &lhs=step.full_lhs;
    if (ID_symbol != lhs.id()) continue;
    const std::string &id=id2string(to_symbol_expr(lhs).get_identifier());
    if (CEGIS_CONTROL_SOLUTION_VAR_NAME != id) continue;
    return to_struct_expr(step.full_lhs_value);
  }
  assert(!"Control solution not found in trace.");
}
}

void convert(control_solutiont &current_candidate, const goto_tracet &trace)
{
}

void show_candidate(messaget::mstreamt &os, const control_solutiont &candidate)
{

}
