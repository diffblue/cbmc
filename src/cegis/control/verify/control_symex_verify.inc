#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/verify/insert_solution.h>

template<class solutiont>
control_symex_verifyt<solutiont>::control_symex_verifyt(
    const control_programt &original_program) :
    original_program(original_program)
{
}

template<class solutiont>
void control_symex_verifyt<solutiont>::process(const candidatet &candidate)
{
  current_program=original_program;
  goto_functionst &gf=current_program.gf;
  insert_solution(current_program, candidate);
  gf.update();
}

template<class solutiont>
const symbol_tablet &control_symex_verifyt<solutiont>::get_symbol_table() const
{
  return current_program.st;
}

template<class solutiont>
const goto_functionst &control_symex_verifyt<solutiont>::get_goto_functions() const
{
  return current_program.gf;
}

template<class solutiont>
void control_symex_verifyt<solutiont>::convert(
    counterexamplest &counterexamples, const goto_tracet &trace) const
{
  counterexamples.push_back(extract_counterexample(trace));
}

template<class solutiont>
void control_symex_verifyt<solutiont>::show_counterexample(
    messaget::mstreamt &os, const counterexamplet &counterexample) const
{
  show_assignments(os, counterexample);
}
