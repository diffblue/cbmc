#include <functional>

#include <util/options.h>

#include <cegis/options/parameters.h>
#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/refactor/environment/instrument_state_vars.h>
#include <cegis/refactor/nullobject/range_collector.h>
#include <cegis/refactor/preprocessing/refactor_preprocessing.h>

refactor_preprocessingt::refactor_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

void refactor_preprocessingt::operator()()
{
  const symbol_tablet &st=original_program.st;
  goto_functionst &gf=original_program.gf;
  inline_user_program(st, gf);
  if (options.get_bool_option(CEGIS_NULL_OBJECT_REFACTOR))
  {
    collect_nullobject_ranges(original_program);
    for (refactor_programt::sketcht &sketch : original_program.sketches)
    {
      goto_ranget &input_range=sketch.input_range;
      goto_programt &body=get_body(gf, input_range.first);
      const std::function<bool(const goto_programt::instructiont &)> pred=
          [&st, &sketch](const goto_programt::instructiont &instr)
          { return false;};
      instrument_state_vars(body, input_range.first, input_range.second, pred);
    }
    // TODO: collect_
  }
  // TODO: construct_instruction_set(original_program);
  // TODO: Implement
  assert(false);
}

void refactor_preprocessingt::operator()(const size_t max_length) const
{
  // TODO: Implement
  assert(false);
}

size_t refactor_preprocessingt::get_min_solution_size() const
{
  // TODO: Implement
  assert(false);
}
