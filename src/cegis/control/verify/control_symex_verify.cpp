#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/verify/insert_solution.h>
#include <cegis/control/verify/control_symex_verify.h>

control_symex_verifyt::control_symex_verifyt(
    const control_programt &original_program) :
    original_program(original_program)
{
}

void control_symex_verifyt::process(const candidatet &candidate)
{
  current_program=original_program;
  goto_functionst &gf=current_program.gf;
  insert_solution(current_program, candidate);
  gf.update();
}

const symbol_tablet &control_symex_verifyt::get_symbol_table() const
{
  return current_program.st;
}

const goto_functionst &control_symex_verifyt::get_goto_functions() const
{
  return current_program.gf;
}

void control_symex_verifyt::convert(counterexamplest &counterexamples,
    const goto_tracet &trace) const
{
  counterexamples.push_back(extract_counterexample(trace));
}

void control_symex_verifyt::show_counterexample(messaget::mstreamt &os,
    const counterexamplet &counterexample) const
{
  show_assignments(os, counterexample);
}
