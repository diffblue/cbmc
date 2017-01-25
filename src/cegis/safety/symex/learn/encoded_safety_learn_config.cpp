/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/value/program_individual_serialisation.h>
#include <cegis/safety/symex/learn/solution_factory.h>
#include <cegis/safety/symex/learn/encoded_safety_learn_config.h>

encoded_safety_learn_configt::encoded_safety_learn_configt(
    safety_learn_configt &config) :
    config(config)
{
}

encoded_safety_learn_configt::~encoded_safety_learn_configt()
{
}

void encoded_safety_learn_configt::process(
    const counterexamplest &counterexamples, const size_t max_solution_size)
{
  config.process(counterexamples, max_solution_size);
}

void encoded_safety_learn_configt::set_word_width(
    const size_t word_width_in_bits)
{
  config.set_word_width(word_width_in_bits);
}

const symbol_tablet &encoded_safety_learn_configt::get_symbol_table() const
{
  return config.get_symbol_table();
}

const goto_functionst &encoded_safety_learn_configt::get_goto_functions() const
{
  return config.get_goto_functions();
}

void encoded_safety_learn_configt::convert(candidatet &candidate,
    const class goto_tracet &trace, const size_t max_solution_size)
{
  const invariant_programt &prog=config.get_safety_program();
  candidate=to_program_individual(prog, trace);
}

void encoded_safety_learn_configt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  safety_goto_solutiont converted;
  const symbol_tablet &st=get_symbol_table();
  const goto_functionst &gf=get_goto_functions();
  const safety_learn_configt::invariant_variable_idst &vars=config.get_vars();
  create_safety_solution(converted, st, gf, candidate, vars);
  config.show_candidate(os, converted);
}

size_t encoded_safety_learn_configt::get_num_vars() const
{
  return config.get_num_vars();
}

size_t encoded_safety_learn_configt::get_num_consts() const
{
  return config.get_num_consts();
}
