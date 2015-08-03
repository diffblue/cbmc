#include <sstream>
#include <algorithm>
#include <util/options.h>
#include <util/arith_tools.h>
#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>
#include <goto-programs/goto_convert.h>
#include <cbmc/bmc.h>
#include <cegis/options/literals.h>
#include <cegis/options/cegis_options.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/variables_factory.h>
#include <cegis/symex/candidate_factory.h>
#include <cegis/symex/symex_learning_program_adapter.h>
#include <cegis/symex/symex_learn.h>

symex_learnt::symex_learnt(const cegis_optionst &options,
    const symbol_tablet &symbol_table, const goto_functionst &goto_functions,
    ui_message_handlert &ui_message_handler) :
    options(options), symbol_table(symbol_table), goto_functions(
        goto_functions), ui_message_handler(ui_message_handler)
{
}

symex_learnt::~symex_learnt()
{
}

symex_learnt::candidatet symex_learnt::next_candidate() const
{
  return candidate;
}

bool symex_learnt::learn(const counterexamplet &counterexample)
{
  candidate.clear();
  counterexamples.push_back(counterexample);
  symex_learning_program_adaptert program_adapter(symbol_table, goto_functions,
      options, ui_message_handler, counterexamples);
  program_adapter();
  const goto_functionst &new_gf=program_adapter.get_adapted_goto_functions();
  const symbol_tablet &new_st=program_adapter.get_adapted_symbol_table();
  optionst learn_options(options.get_options());
  learn_options.set_option("unwinding-assertions", false);
  bmct bmc(learn_options, new_st, ui_message_handler);
  const safety_checkert::resultt bmc_result=bmc(new_gf);
  if (safety_checkert::UNSAFE != bmc_result) return false;
  const goto_tracet &trace=bmc.safety_checkert::error_trace;
  candidate_factoryt candidate_factory(candidate, new_gf, trace);
  return candidate_factory();
}

namespace {
class named_body_printert
{
  const goto_programt &printer;
  const namespacet &ns;
  messaget::mstreamt &os;
public:
  named_body_printert(const goto_programt &printer, const namespacet &ns,
      messaget::mstreamt &os) :
      printer(printer), ns(ns), os(os)
  {
  }
  ~named_body_printert()
  {
  }
  void operator()(
      const std::pair<const irep_idt, goto_programt::instructionst> &named_body) const
  {
    const irep_idt &name=named_body.first;
    const goto_programt::instructionst &instr=named_body.second;
    for (goto_programt::const_targett it=instr.begin(); it != instr.end(); ++it)
      printer.output_instruction(ns, name, os, it);
  }
};
}

void symex_learnt::show_candidate(messaget::mstreamt &os) const
{
  const std::string synthesis_entry(options.entry_function_name());
  const goto_programt &entry=get_program_body(goto_functions, synthesis_entry);
  const namespacet ns(symbol_table);
  const named_body_printert printer(entry, ns, os);
  std::for_each(candidate.begin(), candidate.end(), printer);
  os << messaget::eom;
}
