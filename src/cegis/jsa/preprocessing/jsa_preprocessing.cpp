/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/inline_user_program.h>

#include <cegis/jsa/instrument/temps_helper.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/preprocessing/collect_variables.h>
#include <cegis/jsa/preprocessing/create_temp_variables.h>
#include <cegis/jsa/preprocessing/default_jsa_constant_strategy.h>
#include <cegis/jsa/preprocessing/remove_loop.h>
#include <cegis/jsa/preprocessing/jsa_preprocessing.h>

jsa_preprocessingt::jsa_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

jsa_preprocessingt::~jsa_preprocessingt()
{
}

void jsa_preprocessingt::operator()()
{
  goto_functionst &gf=original_program.gf;
  symbol_tablet &st=original_program.st;
  inline_user_program(st, gf);
  remove_loop(original_program);
  original_program.synthetic_variables=default_jsa_constant_strategy(st, gf);
  add_jsa_constraint_meta_variables(original_program);
  add_inductive_step_renondets(original_program);
  clone_heap(original_program);
  collect_counterexample_vars(original_program);
  gf.update();
}

void jsa_preprocessingt::operator()(const size_t max_length)
{
  current_program=original_program;
  goto_functionst &gf=current_program.gf;
  create_jsa_temp_variables(current_program, max_length);
  add_zero_jsa_temps_to_pred_exec(current_program);
  gf.update();
}

size_t jsa_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

const jsa_programt &jsa_preprocessingt::get_jsa_program() const
{
  return current_program;
}
