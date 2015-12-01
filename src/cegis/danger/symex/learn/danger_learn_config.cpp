#include <algorithm>

#include <cegis/danger/options/danger_program_printer.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/danger_library.h>
#include <cegis/danger/symex/learn/add_programs_to_learn.h>
#include <cegis/danger/symex/learn/add_counterexamples.h>
#include <cegis/danger/symex/learn/add_x0_placeholders.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/learn/danger_learn_config.h>

danger_learn_configt::danger_learn_configt(const danger_programt &program) :
    original_program(program), num_consts(0u)
{
}

danger_learn_configt::~danger_learn_configt()
{
}

void danger_learn_configt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  program=original_program;
  var_ids.clear();
  num_consts=get_danger_variable_ids(program.st, var_ids);
  const size_t num_vars=var_ids.size();
  null_message_handlert msg;
  add_danger_library(program, msg, num_vars, num_consts, max_solution_size);
  danger_add_variable_refs(program, var_ids, max_solution_size);
  danger_add_programs_to_learn(program, max_solution_size);
  danger_add_x0_placeholders(program);
  danger_add_learned_counterexamples(program, counterexamples);
  program.gf.update();
}

void danger_learn_configt::set_word_width(const size_t word_width_in_bits)
{
  restrict_bv_size(program, word_width_in_bits);
  program.gf.update();
}

const symbol_tablet &danger_learn_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &danger_learn_configt::get_goto_functions() const
{
  return program.gf;
}

const danger_programt &danger_learn_configt::get_danger_program() const
{
  return program;
}

void danger_learn_configt::convert(candidatet &candidate,
    const class goto_tracet &trace, const size_t max_solution_size)
{
  candidate.danger_programs.clear();
  candidate.x0_choices.clear();
  create_danger_solution(candidate, program, trace, var_ids, max_solution_size);
}

void danger_learn_configt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  print_danger_program(os, program, candidate);
}

const danger_learn_configt::danger_variable_idst &danger_learn_configt::get_vars() const
{
  return var_ids;
}

size_t danger_learn_configt::get_num_vars() const
{
  return var_ids.size();
}

size_t danger_learn_configt::get_num_consts() const
{
  return num_consts;
}
