/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_convert.h>

#include <cbmc/bmc.h>

#include <cegis/bmc/bmc_verification_oracle.h>

bmc_verification_oraclet::bmc_verification_oraclet(const optionst &options,
    const symbol_tablet &symbol_table, const goto_functionst &goto_functions,
    ui_message_handlert &ui_message_handler) :
    is_failure(false), options(options), symbol_table(symbol_table), goto_functions(
        goto_functions), ui_message_handler(ui_message_handler)
{
}

bmc_verification_oraclet::~bmc_verification_oraclet()
{
}

namespace {
class add_instructiont
{
  goto_programt &program;
public:
  add_instructiont(goto_programt &program) :
      program(program)
  {
  }
  void operator()(const goto_programt::instructiont &rhs) const
  {
    goto_programt::instructiont &lhs(*program.add_instruction(rhs.type));
    lhs.guard=rhs.guard;
    lhs.code=rhs.code;
  }
};

class insert_bodyt
{
  typedef bmc_verification_oraclet::candidatet::value_type body_typet;
  goto_functionst &goto_functions;
public:
  insert_bodyt(goto_functionst &goto_functions) :
      goto_functions(goto_functions)
  {
  }
  void operator()(const body_typet &body) const
  {
    const irep_idt &function_name=body.first;
    goto_functionst::function_mapt &fm=goto_functions.function_map;
    goto_functionst::function_mapt::iterator f=fm.find(function_name);
    assert(fm.end() != f);
    assert(!f->second.body_available);
    const add_instructiont add_instruction(f->second.body);
    const goto_programt::instructionst &instructions(body.second);
    std::for_each(instructions.begin(), instructions.end(), add_instruction);
    f->second.body_available=true;
  }
};

const char INPUT_PREFIX[]="__CPROVER_synthesis_arg";
class build_counterexamplet
{
  bmc_verification_oraclet::counterexamplet &input_values;
public:
  build_counterexamplet(bmc_verification_oraclet::counterexamplet &ce) :
      input_values(ce)
  {
  }

  void operator()(const goto_tracet::stepst::value_type &step) const
  {
    if (!step.is_assignment()) return;
    if (step.pc->source_location.get_file().empty()) return;
    const irep_idt &symbol_id(step.lhs_object.get_identifier());
    // TODO: Handle global variables
    if (id2string(symbol_id).find(INPUT_PREFIX) == std::string::npos) return;
    input_values[symbol_id]=step.full_lhs_value;
  }
};
}

void bmc_verification_oraclet::verify(const candidatet &candidate)
{
  current_counterexample.clear();
  goto_functionst goto_functions;
  goto_functions.copy_from(this->goto_functions);
  const insert_bodyt insert_body(goto_functions);
  std::for_each(candidate.begin(), candidate.end(), insert_body);
  bmct bmc(options, symbol_table, ui_message_handler);
  const safety_checkert::resultt bmc_result=bmc(goto_functions);
  switch (bmc_result)
  {
  case safety_checkert::ERROR:
    is_failure=true;
  case safety_checkert::SAFE:
    return;
  default:
    const goto_tracet::stepst &trace=bmc.safety_checkert::error_trace.steps;
    const build_counterexamplet build_ce(current_counterexample);
    std::for_each(trace.begin(), trace.end(), build_ce);
  }
}

bmc_verification_oraclet::counterexamplet bmc_verification_oraclet::get_counterexample() const
{
  return current_counterexample;
}

bool bmc_verification_oraclet::has_counterexample() const
{
  return !current_counterexample.empty();
}

bool bmc_verification_oraclet::success() const
{
  return !is_failure;
}
