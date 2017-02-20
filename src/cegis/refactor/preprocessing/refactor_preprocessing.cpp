/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <functional>

#include <util/options.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/refactor/options/refactoring_type.h>
#include <cegis/refactor/constraint/constraint_factory.h>
#include <cegis/refactor/environment/instrument_state_vars.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>
#include <cegis/refactor/nullobject/nullable_analysis.h>
#include <cegis/refactor/nullobject/range_collector.h>
#include <cegis/refactor/preprocessing/collect_counterexamples.h>
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
  const refactoring_typet type(get_refactoring_type(options));
  switch(type)
  {
  case refactoring_typet::NULL_OBJECT:
    collect_nullobject_ranges(original_program);
    break;
  }
  create_constraint_function_caller(original_program);
  for(refactor_programt::sketcht &s : original_program.sketches)
  {
    collect_state_vars(s.state_vars, s.spec_range.first, s.spec_range.second);
    collect_state_vars(s.state_vars, s.input_range.first, s.input_range.second);
  }
  switch(type)
  {
  case refactoring_typet::NULL_OBJECT:
    const std::set<irep_idt> null_meths(get_nullable_methods(original_program));
    for(const irep_idt &m : null_meths)
    {
      const cegis_operand_datat op_data(get_operand_signature(st, m));
      const std::string proc(create_cegis_processor(st, gf, op_data));
      const std::string prog(declare_cegis_program(st, gf, proc));
      original_program.programs.insert(prog);
      for(refactor_programt::sketcht &s : original_program.sketches)
      {
        const goto_programt::targett first=s.input_range.first;
        const goto_programt::targett last=s.input_range.second;
        replace_method_call_by_processor(st, gf, first, last, m, proc, prog);
      }
    }
    break;
  }
  create_refactoring_constraint(original_program);
  collect_counterexamples(original_program);
}

namespace
{
void set_cegis_processor_sizes(const symbol_tablet &st,
    const goto_ranget &range, const size_t size)
{
  set_cegis_processor_sizes(st, range.first, range.second, size);
}
}

void refactor_preprocessingt::operator()(const size_t max_length)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  set_cegis_processor_sizes(st, max_length);
  for(const refactor_programt::sketcht &sketch : current_program.sketches)
  {
    set_cegis_processor_sizes(st, sketch.input_range, max_length);
    set_cegis_processor_sizes(st, sketch.spec_range, max_length);
  }
}

size_t refactor_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

const refactor_programt &refactor_preprocessingt::get_program() const
{
  return current_program;
}
