#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/learn/constraint_helper.h>
#include <cegis/refactor/learn/instrument_counterexamples.h>
#include <cegis/refactor/learn/refactor_symex_learn.h>

refactor_symex_learnt::refactor_symex_learnt(
    const refactor_programt &original_program) :
    original_program(original_program)
{
}

void refactor_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  current_program=original_program;
  transform_asserts_to_assumes(current_program.gf);
  instrument_counterexamples(current_program, counterexamples);
}

const symbol_tablet &refactor_symex_learnt::get_symbol_table() const
{
  return current_program.st;
}

const goto_functionst &refactor_symex_learnt::get_goto_functions() const
{
  return current_program.gf;
}

void refactor_symex_learnt::set_word_width(
    const size_t word_width_in_bits) const
{
}

void refactor_symex_learnt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  // TODO: Implement
  assert(false);
}

void refactor_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  // TODO: Implement
  assert(false);
}
