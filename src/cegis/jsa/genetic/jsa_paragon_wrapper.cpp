/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/converters/solution.h>
#include <cegis/jsa/learn/extract_candidate.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>
#include <cegis/jsa/genetic/jsa_paragon_wrapper.h>

jsa_paragon_wrappert::jsa_paragon_wrappert(jsa_symex_learnt &wrapped) :
    wrapped(wrapped)
{
}

void jsa_paragon_wrappert::process(const counterexamplest &counterexamples,
    const size_t max_solution_size) const
{
  wrapped.process(counterexamples, max_solution_size);
}

void jsa_paragon_wrappert::process(const size_t max_solution_size) const
{
  wrapped.process(max_solution_size);
}

void jsa_paragon_wrappert::set_word_width(const size_t word_width_in_bits) const
{
  wrapped.set_word_width(word_width_in_bits);
}

void jsa_paragon_wrappert::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  const jsa_programt &prog=wrapped.get_jsa_program();
  extract_jsa_genetic_candidate(current_candidate, prog, trace);
  current_candidate.fitness=0;
}

const symbol_tablet &jsa_paragon_wrappert::get_symbol_table() const
{
  return wrapped.get_symbol_table();
}

const goto_functionst &jsa_paragon_wrappert::get_goto_functions() const
{
  return wrapped.get_goto_functions();
}

void jsa_paragon_wrappert::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  const jsa_programt &prog=wrapped.get_jsa_program();
  wrapped.show_candidate(os, ::convert(candidate, prog));
}
