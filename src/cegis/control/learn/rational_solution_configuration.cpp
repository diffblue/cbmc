#include <ansi-c/expr2c.h>
#include <goto-programs/goto_trace.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/nondet_solution.h>
#include <cegis/control/learn/rational_solution_configuration.h>

void rational_solution_configurationt::nondeterminise_solution_configuration(
    symbol_tablet &st, goto_functionst &gf)
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

void rational_solution_configurationt::convert(
    control_solutiont &current_candidate, const goto_tracet &trace,
    const symbol_tablet &st)
{
  const struct_exprt &solution=find_solution(trace);
  const namespacet ns(st);
  current_candidate.a=get_a_controller_comp(ns, solution);
  current_candidate.b=get_b_controller_comp(ns, solution);
}

namespace
{
void print_array(messaget::mstreamt &os, const array_exprt &array,
    const char * const name, const symbol_tablet &st)
{
  const namespacet ns(st);
  const array_exprt::operandst &ops=array.operands();
  os << '<' << name << '>' << messaget::endl;
  for (const array_exprt::operandst::value_type &value : ops)
    os << "<item>" << expr2c(value, ns) << "</item>" << messaget::endl;
  os << "</" << name << '>' << messaget::endl;
  os << '<' << name << "_size>" << ops.size();
  os << "</" << name << "_size>" << messaget::endl;
}
}


void rational_solution_configurationt::show_candidate(messaget::mstreamt &os,
    const control_solutiont &candidate, const symbol_tablet &st)
{
  print_array(os, candidate.a, "a", st);
  print_array(os, candidate.b, "b", st);
}
