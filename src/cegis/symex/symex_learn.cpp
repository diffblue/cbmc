/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <algorithm>

#include <util/options.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>

#include <goto-programs/goto_convert.h>

#include <cbmc/cbmc_solvers.h>
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
    message_handlert &msg) :
    messaget(msg), options(options), symbol_table(symbol_table),
    goto_functions(goto_functions)
{
}

symex_learnt::~symex_learnt()
{
}

symex_learnt::candidatet symex_learnt::next_candidate() const
{
  return candidate;
}

namespace {
void clear_candidate(symex_learnt::candidatet &candidate)
{
  candidate.bodies.clear();
  candidate.constants.clear();
}
}

bool symex_learnt::learn(const counterexamplet &counterexample)
{
  clear_candidate(candidate);
  counterexamples.push_back(counterexample);
  null_message_handlert null_message_handler;
  symex_learning_program_adaptert program_adapter(symbol_table, goto_functions,
      options, null_message_handler, counterexamples);
  program_adapter();
  const goto_functionst &new_gf=program_adapter.get_adapted_goto_functions();
  const symbol_tablet &new_st=program_adapter.get_adapted_symbol_table();
  optionst learn_options(options.get_options());
  learn_options.set_option("unwinding-assertions", false);

  //get solver
  cbmc_solverst cbmc_solvers(learn_options, symbol_table, null_message_handler);
  std::unique_ptr<cbmc_solverst::solvert> cbmc_solver = 
    cbmc_solvers.get_solver();
  prop_convt& prop_conv = cbmc_solver->prop_conv();
  bmct bmc(learn_options, new_st, null_message_handler, prop_conv);

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
  const bool print_name_prefix;
public:
  named_body_printert(const goto_programt &printer, const namespacet &ns,
      messaget::mstreamt &os, const bool print_name_prefix=true) :
      printer(printer), ns(ns), os(os), print_name_prefix(print_name_prefix)
  {
  }
  ~named_body_printert()
  {
  }
  void operator()(
      const std::pair<const irep_idt, goto_programt::instructionst> &named_body) const
  {
    const irep_idt &name=named_body.first;
    if (print_name_prefix) os << name << ": " << messaget::eom;
    const goto_programt::instructionst &instr=named_body.second;
    for (goto_programt::const_targett it=instr.begin(); it != instr.end(); ++it)
      printer.output_instruction(ns, name, os, it);
  }
};

class variable_assignment_printert
{
  const named_body_printert printer;
public:
  variable_assignment_printert(const goto_programt &printer,
      const namespacet &ns, messaget::mstreamt &os) :
      printer(printer, ns, os, false)
  {
  }
  ~variable_assignment_printert()
  {
  }
  void operator()(const std::pair<const irep_idt, exprt> &named_const) const
  {
    const irep_idt &name=named_const.first;
    const exprt &value=named_const.second;
    goto_programt::instructiont instr;
    instr.type=ASSIGN;
    instr.source_location=value.location();
    const symbol_exprt lhs(name, value.type());
    instr.code=code_assignt(lhs, value);
    const goto_programt::instructionst instrs(1, instr);
    printer(std::make_pair(name, instrs));
  }
};
}

void symex_learnt::show_candidate(messaget::mstreamt &os) const
{
  const std::string synthesis_entry(options.entry_function_name());
  const goto_programt &entry=get_program_body(goto_functions, synthesis_entry);
  const namespacet ns(symbol_table);
  const candidatet::constantst &constants=candidate.constants;
  const variable_assignment_printert ass_printer(entry, ns, os);
  std::for_each(constants.begin(), constants.end(), ass_printer);
  const candidatet::bodiest &bodies=candidate.bodies;
  const named_body_printert printer(entry, ns, os);
  std::for_each(bodies.begin(), bodies.end(), printer);
  os << messaget::eom;
}
