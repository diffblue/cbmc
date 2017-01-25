/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/expr_util.h>

#include <cegis/danger/meta/literals.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/cegis_library.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/invariant/symex/learn/add_invariant_programs_to_learn.h>
#include <cegis/safety/symex/learn/add_counterexamples.h>
#include <cegis/safety/value/safety_goto_ce.h>
#include <cegis/safety/options/safety_program_printer.h>
#include <cegis/safety/constraint/safety_constraint_factory.h>
#include <cegis/safety/symex/learn/add_variable_refs.h>
#include <cegis/safety/symex/learn/solution_factory.h>
#include <cegis/safety/symex/learn/safety_learn_config.h>

safety_learn_configt::safety_learn_configt(const safety_programt &program) :
    original_program(program), num_consts(0)
{
}

safety_learn_configt::~safety_learn_configt()
{
}

void safety_learn_configt::process(const counterexamplest &ces,
    const size_t max_sz)
{
  program=original_program;
  var_ids.clear();
  symbol_tablet &st=program.st;
  num_consts=get_invariant_variable_ids(st, var_ids);
  const size_t num_vars=var_ids.size();
  null_message_handlert msg;
  const std::string name(DANGER_EXECUTE);
  goto_functionst &gf=program.gf;
  add_cegis_library(st, gf, msg, num_vars, num_consts, max_sz, name);
  add_safety_learning_variable_refs(program, var_ids, max_sz);
  link_result_var(st, gf, var_ids.size(), max_sz, program.Ix0);
  add_invariant_progs_to_learn(program, max_sz);
  const invariant_programt &prog=program;
  const invariant_programt::const_invariant_loopst loops(prog.get_loops());
  const invariant_programt::invariant_loopt &first_loop=*loops.front();
  const std::string I0=get_prog_var_name(st, first_loop.meta_variables.Ix);
  execute_inv_prog(st, gf, max_sz, program.Ix0, I0);
  safety_add_learned_counterexamples(program, ces, create_safety_constraint);
  gf.update();
}

void safety_learn_configt::process(const size_t max_solution_size)
{
  constraint_varst ce_vars;
  get_invariant_constraint_vars(ce_vars, original_program);
  const typet type(cegis_default_integer_type());  // XXX: Currently single data type
  const exprt zero(gen_zero(type));
  counterexamplet dummy_ce;
  dummy_ce.x.push_back(counterexamplet::assignmentst());
  counterexamplet::assignmentst &x=dummy_ce.x.front();
  for (const symbol_exprt &var : ce_vars)
    x.insert(std::make_pair(var.get_identifier(), zero));
  // TODO: Implement for multiple loops (change constraint, instrumentation)
  const safety_programt &prog=original_program;
  const invariant_programt::const_invariant_loopst loops=prog.get_loops();
  assert(!loops.empty());
  // XXX: We might have to handle skolem choices explicitly at some point
  for (const goto_programt::targett &skolem_choice : loops.front()->skolem_choices)
    x.insert(std::make_pair(get_affected_variable(*skolem_choice), zero));
  counterexamplet::assignmentst &x0=dummy_ce.x0;
  for (const goto_programt::targett &x0_choice : original_program.x0_choices)
    x0.insert(std::make_pair(get_affected_variable(*x0_choice), zero));
  counterexamplest empty(1, dummy_ce);
  process(empty, max_solution_size);
}

void safety_learn_configt::set_word_width(const size_t word_width_in_bits)
{
  // TODO: Implement!
}

const symbol_tablet &safety_learn_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &safety_learn_configt::get_goto_functions() const
{
  return program.gf;
}

const safety_programt &safety_learn_configt::get_safety_program() const
{
  return program;
}

void safety_learn_configt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_sz)
{
  create_safety_solution(current_candidate, program, trace, var_ids, max_sz);
}

void safety_learn_configt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  print_safety_program(os, program, candidate);
}

const safety_learn_configt::invariant_variable_idst &safety_learn_configt::get_vars() const
{
  return var_ids;
}

size_t safety_learn_configt::get_num_vars() const
{
  return var_ids.size();
}

size_t safety_learn_configt::get_num_consts() const
{
  return num_consts;
}
