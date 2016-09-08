#include <cegis/control/learn/control_symex_learn.h>

control_symex_learnt::control_symex_learnt(
    const control_programt &original_program) :
    original_program(original_program)
{
}

void control_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size) const
{
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

void control_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  // TODO: Implement
  assert(false);
}
