/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <numeric>

#include <util/options.h>
#include <util/message.h>

#include <goto-programs/goto_inline.h>

#include <cegis/invariant/preprocess/remove_loops_and_assertion.h>
#include <cegis/invariant/preprocess/add_invariants_and_temp_variables.h>
#include <cegis/invariant/meta/meta_variable_names.h>
// TODO: Move to invariant folder
#include <cegis/danger/preprocess/store_nondet_choices.h>
#include <cegis/safety/meta/meta_variable_names.h>
#include <cegis/safety/preprocessing/safety_preprocessing.h>

safety_preprocessingt::safety_preprocessingt(optionst &options,
    const symbol_tablet &st, const goto_functionst &gf,
    const constant_strategyt &constant_strategy) :
    options(options), original_program(st, gf), constant_strategy(
        constant_strategy)
{
}

safety_preprocessingt::~safety_preprocessingt()
{
}

size_t safety_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

namespace
{
void add_choice_labels(const goto_programt::targetst &choices, size_t offset=0)
{
  for (const goto_programt::targett &choice : choices)
  {
    goto_programt::instructiont::labelst &labels=choice->labels;
    std::string label(DANGER_CE_QUANTIFIER_LABEL_PREFIX);
    label+=integer2string(offset++);
    labels.push_back(label);
  }
}

void add_skolem_labels(const invariant_programt &prog)
{
  size_t offset=0;
  const invariant_programt::const_invariant_loopst loops(prog.get_loops());
  for (const invariant_programt::invariant_loopt * const loop : loops)
  {
    add_choice_labels(loop->skolem_choices, offset);
    offset+=loop->skolem_choices.size();
  }
}
}

void safety_preprocessingt::operator ()()
{
  const namespacet ns(original_program.st);
  null_message_handlert null_msg;
  goto_functionst &gf=original_program.gf;
  goto_inline(gf, ns, null_msg);
  invariant_remove_loops_and_assertion(original_program);
  store_skolem_choices(original_program);
  add_skolem_labels(original_program);
  gf.update();
  current_program=original_program;
}

size_t get_x0_offset(const invariant_programt &prog)
{
  const invariant_programt::const_invariant_loopst l(prog.get_loops());
  return std::accumulate(l.begin(), l.end(), 0,
      [](const size_t sum, const invariant_programt::invariant_loopt * const loop)
      { return sum + loop->skolem_choices.size();});
}

void safety_preprocessingt::operator ()(const size_t max_length)
{
  current_program=original_program;
  const unsigned int max_width=constant_strategy(current_program, max_length);
  options.set_option("max-constant-width", max_width);
  store_x0_choices(current_program);
  add_choice_labels(current_program.x0_choices, get_x0_offset(current_program));
  create_tmp_variables(current_program, max_length);
  add_invariant_variables(current_program, get_Ix0(), get_Ix, get_Ix_prime);
}

const safety_programt &safety_preprocessingt::get_safety_program() const
{
  return current_program;
}
