#include <util/options.h>

#include <goto-programs/goto_inline.h>

#include <cegis/invariant/preprocess/remove_loops_and_assertion.h>
#include <cegis/invariant/preprocess/add_invariants_and_temp_variables.h>
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

void safety_preprocessingt::operator ()()
{
  const namespacet ns(original_program.st);
  null_message_handlert null_msg;
  goto_functionst &gf=original_program.gf;
  goto_inline(gf, ns, null_msg);
  invariant_remove_loops_and_assertion(original_program);
  store_skolem_choices(original_program);
  gf.update();
  current_program=original_program;
}

void safety_preprocessingt::operator ()(const size_t max_length)
{
  current_program=original_program;
  const unsigned int max_width=constant_strategy(current_program, max_length);
  options.set_option("max-constant-width", max_width);
  store_x0_choices(current_program);
  create_tmp_variables(current_program, max_length);
  add_invariant_variables(current_program, get_Ix0(), get_Ix, get_Ix_prime);
}

const safety_programt &safety_preprocessingt::get_safety_program() const
{
  return current_program;
}
