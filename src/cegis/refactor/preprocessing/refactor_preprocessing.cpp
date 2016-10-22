#include <functional>

#include <util/options.h>

#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/refactor/options/refactoring_type.h>
#include <cegis/refactor/environment/instrument_state_vars.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>
#include <cegis/refactor/nullobject/range_collector.h>
#include <cegis/refactor/preprocessing/refactor_preprocessing.h>

refactor_preprocessingt::refactor_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

void refactor_preprocessingt::operator()()
{
  symbol_tablet &st=original_program.st;
  goto_functionst &gf=original_program.gf;
  inline_user_program(st, gf);
  const refactoring_typet type(get_refactoring_type(options));
  switch (type)
  {
  case refactoring_typet::NULL_OBJECT:
    collect_nullobject_ranges(original_program);
    // TODO: Insert GOTOs between ranges
    break;
  }
  for (refactor_programt::sketcht &s : original_program.sketches)
  {
    s.state_vars=collect_state_vars(s.spec_range.first, s.spec_range.second);
    const std::map<typet, size_t> slots(slots_per_type(st, s.state_vars));
    s.processor_function=create_cegis_processor(st, gf, slots);
  }
  assert(false);
  // TODO: Insert extern programs.
  switch (type)
  {
  case refactoring_typet::NULL_OBJECT:
    // TODO: Replace method calls by program execution.
    // TODO: Instrument ops (globals + params from corresponding replaced method call)
    break;
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
