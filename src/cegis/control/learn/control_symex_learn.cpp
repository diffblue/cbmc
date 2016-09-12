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
  const symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  nondet_control_solution(st, gf);
  // TODO: Implement
  assert(false);
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

void control_symex_learnt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  // TODO: Implement
  assert(false);
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
