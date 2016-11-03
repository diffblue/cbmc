#include <functional>

#include <util/options.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/refactor/options/refactoring_type.h>
#include <cegis/refactor/environment/instrument_state_vars.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>
#include <cegis/refactor/nullobject/nullable_analysis.h>
#include <cegis/refactor/nullobject/range_collector.h>
#include <cegis/refactor/preprocessing/refactor_preprocessing.h>

// XXX: Debug
#include <iostream>
// XXX: Debug

refactor_preprocessingt::refactor_preprocessingt(const optionst &options,
    const symbol_tablet &st, const goto_functionst &gf) :
    options(options), original_program(st, gf)
{
}

void refactor_preprocessingt::operator()()
{
  symbol_tablet &st=original_program.st;
  goto_functionst &gf=original_program.gf;
  const refactoring_typet type(get_refactoring_type(options));
  switch (type)
  {
  case refactoring_typet::NULL_OBJECT:
    collect_nullobject_ranges(original_program);
    break;
  }
  for (refactor_programt::sketcht &s : original_program.sketches)
  {
    collect_state_vars(s.state_vars, s.spec_range.first, s.spec_range.second);
    collect_state_vars(s.state_vars, s.input_range.first, s.input_range.second);
  }
  switch (type)
  {
  case refactoring_typet::NULL_OBJECT:
    const std::set<irep_idt> null_meths(get_nullable_methods(original_program));
    for (const irep_idt &m : null_meths)
    {
      const cegis_operand_datat op_data(get_operand_signature(st, m));
      const std::string proc(create_cegis_processor(st, gf, op_data));
      const std::string prog(declare_cegis_program(st, gf, proc));
      for (refactor_programt::sketcht &s : original_program.sketches)
      {
        const goto_programt::targett first=s.input_range.first;
        const goto_programt::targett last=s.input_range.second;
        goto_programt &body=get_body(gf, first);
        replace_method_call_by_processor(st, body, first, last, m, proc, prog);
      }
    }
    break;
  }
  // TODO: Generate constraint per sketch using input/spec range:
  // * Nondet used variables
  // * Clone used variables
  // * Replace used variables in input range by clones
  // * Goto input/spec range
  //   * Repeat possibly skipped local declarations
  // * Generate assertion based on used variables

  // XXX: Debug
  std::cout << "<refactor_preprocessingt>" << std::endl;
  original_program.gf.output(namespacet(original_program.st), std::cout);
  std::cout << "</refactor_preprocessingt>" << std::endl;
  // XXX: Debug
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
