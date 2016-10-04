#include <util/options.h>

#include <cegis/options/parameters.h>
#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/refactor/nullobject/range_collector.h>
#include <cegis/refactor/preprocessing/refactor_preprocessing.h>

refactor_preprocessingt::refactor_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

void refactor_preprocessingt::operator()()
{
  inline_user_program(original_program.st, original_program.gf);
  if (options.get_bool_option(CEGIS_NULL_OBJECT_REFACTOR))
  {
    collect_nullobject_ranges(original_program);
  }
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
