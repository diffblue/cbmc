#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/learn/constraint_helper.h>
#include <cegis/learn/insert_counterexample.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/float_helper.h>
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

const array_exprt &get_a(const namespacet &ns, const struct_exprt &solution)
{
  return to_array_expr(
      get_controller_comp(ns, solution, CEGIS_CONTROL_A_MEMBER_NAME));
}

const array_exprt &get_b(const namespacet &ns, const struct_exprt &solution)
{
  return to_array_expr(
      get_controller_comp(ns, solution, CEGIS_CONTROL_B_MEMBER_NAME));
}

void extract(std::vector<double> &data, const array_exprt &array)
{
  const exprt::operandst &ops=array.operands();
  const size_t size=ops.size();
  data.resize(size);
  for (size_t i=0; i < size; ++i)
    data[i]=to_control_float(to_constant_expr(ops[i]));
}
}

void control_symex_learnt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  const struct_exprt &solution=find_solution(trace);
  const namespacet ns(current_program.st);
  extract(current_candidate.a, get_a(ns, solution));
  extract(current_candidate.b, get_b(ns, solution));
}

namespace
{
void print_array(messaget::mstreamt &os, const std::vector<double> &array,
    const char * const name)
{
  os << '<' << name << '>' << messaget::endl;
  for (const double value : array)
    os << "<item>" << value << "</item>" << messaget::endl;
  os << "</" << name << '>' << messaget::endl;
  os << '<' << name << "_size>" << array.size();
  os << "</" << name << "_size>" << messaget::endl;
}
}

void control_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  print_array(os, candidate.a, "a");
  print_array(os, candidate.b, "b");
}
