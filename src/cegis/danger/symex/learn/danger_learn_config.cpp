/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>

#include <cegis/instrument/cegis_library.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>
#include <cegis/invariant/symex/learn/add_counterexamples.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program_printer.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/add_programs_to_learn.h>
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

void danger_learn_configt::process(const counterexamplest &ces,
    const size_t max_sz)
{
  program=original_program;
  var_ids.clear();
  num_consts=get_invariant_variable_ids(program.st, var_ids);
  const size_t num_vars=var_ids.size();
  null_message_handlert msg;
  const std::string name(DANGER_EXECUTE);
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  add_cegis_library(st, gf, msg, num_vars, num_consts, max_sz, name);
  link_user_program_variables(program, var_ids);
  link_meta_variables(program, var_ids.size(), max_sz);
  danger_add_programs_to_learn(program, max_sz);
  danger_add_x0_placeholders(program);
  const danger_constraint constr(program.use_ranking);
  invariant_add_learned_counterexamples(program, ces, std::cref(constr), true);
  gf.update();
}

void danger_learn_configt::process(const size_t max_solution_size)
{
  constraint_varst ce_vars;
  get_invariant_constraint_vars(ce_vars, original_program);
  counterexamplet dummy_ce;
  const typet type(cegis_default_integer_type());  // XXX: Currently single data type
  const exprt zero(from_integer(0, type));
  for(const symbol_exprt &var : ce_vars)
    dummy_ce.insert(std::make_pair(var.get_identifier(), zero));
  counterexamplest empty(1, dummy_ce);
  process(empty, max_solution_size);
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

const danger_learn_configt::invariant_variable_idst &danger_learn_configt::get_vars() const
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
