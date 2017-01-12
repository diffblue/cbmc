#include <cegis/learn/constraint_helper.h>
#include <cegis/learn/insert_counterexample.h>

template<class solution_configt>
control_symex_learnt<solution_configt>::control_symex_learnt(
    const control_programt &original_program) :
    original_program(original_program)
{
}

template<class solution_configt>
void control_symex_learnt<solution_configt>::process(
    const counterexamplest &counterexamples, const size_t max_solution_size)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  solution_configt::nondeterminise_solution_configuration(st, gf);
  transform_asserts_to_assumes(gf);
  const goto_programt::targetst &ce_locs=
      current_program.counterexample_locations;
  insert_counterexamples(st, gf, counterexamples, ce_locs);
  gf.update();
}

template<class solution_configt>
const symbol_tablet &control_symex_learnt<solution_configt>::get_symbol_table() const
{
  return current_program.st;
}

template<class solution_configt>
const goto_functionst &control_symex_learnt<solution_configt>::get_goto_functions() const
{
  return current_program.gf;
}

template<class solution_configt>
void control_symex_learnt<solution_configt>::set_word_width(
    const size_t word_width_in_bits) const
{
}

template<class solution_configt>
void control_symex_learnt<solution_configt>::convert(
    candidatet &current_candidate, const goto_tracet &trace,
    const size_t max_solution_size) const
{
  solution_configt::convert(current_candidate, trace, current_program.st);
}

template<class solution_configt>
void control_symex_learnt<solution_configt>::show_candidate(
    messaget::mstreamt &os, const candidatet &candidate) const
{
  solution_configt::show_candidate(os, candidate, current_program.st);
}
