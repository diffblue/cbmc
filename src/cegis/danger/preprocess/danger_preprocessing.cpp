/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/options.h>
#include <util/message.h>

#include <goto-programs/goto_inline.h>

#include <cegis/invariant/preprocess/remove_loops_and_assertion.h>
#include <cegis/invariant/preprocess/add_invariants_and_temp_variables.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/preprocess/add_ranking_and_skolem_variables.h>
#include <cegis/danger/preprocess/store_nondet_choices.h>
#include <cegis/danger/preprocess/danger_preprocessing.h>

danger_preprocessingt::danger_preprocessingt(optionst &options,
    const symbol_tablet &st, const goto_functionst &gf,
    const constant_strategyt &constant_strategy) :
    options(options), original_program(st, gf,
        !options.get_bool_option("danger-no-ranking")), constant_strategy(
        constant_strategy)
{
}

danger_preprocessingt::~danger_preprocessingt()
{
}

namespace
{
bool cmp(const danger_programt::loopt &lhs, const danger_programt::loopt &rhs)
{
  return lhs.skolem_choices.size() < rhs.skolem_choices.size();
}
}

size_t danger_preprocessingt::get_min_solution_size() const
{
  const danger_programt::loopst &l=original_program.loops;
  size_t sklm=std::max_element(l.begin(), l.end(), &cmp)->skolem_choices.size();
  return std::max(sklm, size_t(1u));
}

void danger_preprocessingt::operator ()()
{
  const namespacet ns(original_program.st);
  null_message_handlert null_msg;
  goto_functionst &gf=original_program.gf;
  goto_inline(gf, ns, null_msg);
  invariant_remove_loops_and_assertion(original_program);
  store_skolem_choices(original_program);
  store_x0_choices(original_program);
  gf.update();
  current_program=original_program;
}

void danger_preprocessingt::operator ()(const size_t max_length)
{
  current_program=original_program;
  const unsigned int max_width=constant_strategy(current_program, max_length);
  options.set_option("max-constant-width", max_width);
  create_tmp_variables(current_program, max_length);
  add_invariant_variables(current_program, get_Dx0(), get_Dx, get_Dx_prime);
  add_ranking_and_skolem_variables(current_program, max_length);
}

const danger_programt &danger_preprocessingt::get_danger_program() const
{
  return current_program;
}
