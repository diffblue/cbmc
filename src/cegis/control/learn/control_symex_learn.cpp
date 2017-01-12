#include <ansi-c/expr2c.h>
#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/learn/constraint_helper.h>
#include <cegis/learn/insert_counterexample.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/nondet_solution.h>
#include <cegis/control/learn/control_symex_learn.h>

control_symex_learnt::control_symex_learnt(
    const control_programt &original_program) :
    original_program(original_program)
{
}

void control_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  nondet_control_solution(st, gf);
  transform_asserts_to_assumes(gf);
  const goto_programt::targetst &ce_locs=
      current_program.counterexample_locations;
  insert_counterexamples(st, gf, counterexamples, ce_locs);
  gf.update();
}

const symbol_tablet &control_symex_learnt::get_symbol_table() const
{
  return current_program.st;
}

const goto_functionst &control_symex_learnt::get_goto_functions() const
{
  return current_program.gf;
}

void control_symex_learnt::set_word_width(const size_t word_width_in_bits) const
{
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

void control_symex_learnt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  const struct_exprt &solution=find_solution(trace);
  const namespacet ns(current_program.st);
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

void control_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  const symbol_tablet &st=current_program.st;
  print_array(os, candidate.a, "a", st);
  print_array(os, candidate.b, "b", st);
}
