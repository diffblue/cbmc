/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/value/program_individual_serialisation.h>

#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/learn/encoded_danger_learn_config.h>

encoded_danger_learn_configt::encoded_danger_learn_configt(
    const danger_programt &program) :
    danger_learn_config(program)
{
}

encoded_danger_learn_configt::~encoded_danger_learn_configt()
{
}

void encoded_danger_learn_configt::process(
    const counterexamplest &counterexamples, const size_t max_solution_size)
{
  danger_learn_config.process(counterexamples, max_solution_size);
}

void encoded_danger_learn_configt::set_word_width(
    const size_t word_width_in_bits)
{
  danger_learn_config.set_word_width(word_width_in_bits);
}

const symbol_tablet &encoded_danger_learn_configt::get_symbol_table() const
{
  return danger_learn_config.get_symbol_table();
}

const goto_functionst &encoded_danger_learn_configt::get_goto_functions() const
{
  return danger_learn_config.get_goto_functions();
}

void encoded_danger_learn_configt::convert(candidatet &candidate,
    const class goto_tracet &trace, const size_t max_solution_size)
{
  const danger_programt &prog=danger_learn_config.get_danger_program();
  candidate=to_program_individual(prog, trace);
}

void encoded_danger_learn_configt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  const danger_programt &prog=danger_learn_config.get_danger_program();
  const danger_learn_configt::invariant_variable_idst &vars=
      danger_learn_config.get_vars();
  danger_goto_solutiont converted;
  create_danger_solution(converted, prog, candidate, vars);
  danger_learn_config.show_candidate(os, converted);
}

size_t encoded_danger_learn_configt::get_num_vars() const
{
  return danger_learn_config.get_num_vars();
}

size_t encoded_danger_learn_configt::get_num_consts() const
{
  return danger_learn_config.get_num_consts();
}
