/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/remove_returns.h>

#include <cegis/value/assignments_printer.h>
#include <cegis/jsa/constraint/jsa_constraint_factory.h>
#include <cegis/jsa/preprocessing/add_synthesis_library.h>
#include <cegis/jsa/learn/instrument_pred_ops.h>
#include <cegis/jsa/verify/extract_counterexample.h>
#include <cegis/jsa/verify/insert_solution.h>
#include <cegis/jsa/verify/renondet_inputs.h>
#include <cegis/jsa/verify/jsa_symex_verify.h>

jsa_symex_verifyt::jsa_symex_verifyt(const jsa_programt &program) :
    original_program(program)
{
}

void jsa_symex_verifyt::process(const candidatet &cand)
{
  program=original_program;
  const goto_programt::targetst pred_ops(collect_pred_ops(program));
  // add_jsa_library(program, cand.max_size, pred_ops);
  instrument_pred_ops(program, pred_ops);
  insert_jsa_constraint(program, false);
  assume_renondet_inputs_valid(program);

  insert_jsa_solution(program, cand);
  remove_returns(program.st, program.gf);
  program.gf.update();
}

const symbol_tablet &jsa_symex_verifyt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &jsa_symex_verifyt::get_goto_functions() const
{
  return program.gf;
}

void jsa_symex_verifyt::convert(counterexamplest &counterexamples,
    const goto_tracet &trace)
{
  counterexamples.push_back(counterexamplet());
  extract(program, counterexamples.back(), trace);
}

void jsa_symex_verifyt::show_counterexample(messaget::mstreamt &os,
    const counterexamplet &counterexample) const
{
  os << "<jsa_counterexample>" << messaget::endl;
  print_assignments(os, get_symbol_table(), counterexample);
  os << "</jsa_counterexample>" << messaget::endl;
}
