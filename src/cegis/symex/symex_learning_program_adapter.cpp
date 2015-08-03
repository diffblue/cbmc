/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <cegis/options/cegis_options.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/cegis_library.h>
#include <cegis/symex/variables_factory.h>
#include <cegis/symex/target_program_factory.h>
#include <cegis/symex/test_case_factory.h>
#include <cegis/symex/symex_learning_program_adapter.h>

symex_learning_program_adaptert::symex_learning_program_adaptert(
    const symbol_tablet &symbol_table, const goto_functionst &goto_functions,
    const cegis_optionst &options, ui_message_handlert &msg,
    const std::deque<counterexamplet> &counterexamples) :
    symbol_table(symbol_table), options(options), msg(msg), counterexamples(
        counterexamples)
{
  gf.copy_from(goto_functions);
}

symex_learning_program_adaptert::~symex_learning_program_adaptert()
{
}

namespace {
exprt get_synthesis_property(const goto_functionst &gf,
    const cegis_optionst &options)
{
  const goto_programt &body=get_program_body(gf, options.entry_function_name());
  const goto_programt::instructionst &instrs(body.instructions);
  const goto_programt::instructionst::const_iterator assertion=std::find_if(
      instrs.begin(), instrs.end(),
      std::mem_fun_ref(&goto_programt::instructiont::is_assert));
  assert(instrs.end() != assertion);
  return assertion->guard;
}

void clean_entry(goto_functionst &gf, const cegis_optionst &options)
{
  // XXX: Create new function instead and use --function for symex learning entry?
  get_program_body(gf, options.entry_function_name()).clear();
}

void end_synthesis_function(goto_functionst &gf, const cegis_optionst &options,
    source_location_factoryt &lfactory)
{
  const std::string synthesis_entry(options.entry_function_name());
  const source_locationt end_location=lfactory(synthesis_entry);
  goto_programt &entry=get_program_body(gf, synthesis_entry);
  entry.add_instruction(END_FUNCTION)->source_location=end_location;
  gf.update();
}
}

void symex_learning_program_adaptert::operator ()()
{
  const exprt synthesis_property=get_synthesis_property(gf, options);
  clean_entry(gf, options);
  add_cegis_library(symbol_table, gf, msg);
  source_location_factoryt lfactory;
  create_symex_learning_variables(symbol_table, gf, options, lfactory);
  add_target_programs(symbol_table, gf, options, lfactory);
  add_symex_test_cases(symbol_table, gf, options, lfactory, synthesis_property,
      counterexamples.begin(), counterexamples.end());
  end_synthesis_function(gf, options, lfactory);
}

const symbol_tablet &symex_learning_program_adaptert::get_adapted_symbol_table() const
{
  return symbol_table;
}

const goto_functionst &symex_learning_program_adaptert::get_adapted_goto_functions() const
{
  return gf;
}
