/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <memory>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_convert.h>

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>

#include <cegis/options/literals.h>
#include <cegis/util/symbol_table_adapter.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/bmc/bmc_verification_oracle.h>

bmc_verification_oraclet::bmc_verification_oraclet(const optionst &options,
    const symbol_tablet &symbol_table, const goto_functionst &goto_functions) :
    is_failure(false), options(options), symbol_table(symbol_table), goto_functions(
        goto_functions)
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
  typedef bmc_verification_oraclet::candidatet::bodiest::value_type body_typet;
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

bool is_part_of_counterexample(const std::string &name)
{
  return std::string::npos != name.find(CPROVER_SYNTHESIS_ARG_PREFIX)
      || std::string::npos != name.find(CPROVER_SYNTHESIS_PRIVATE_ARG_PREFIX);
}

class build_counterexamplet
{
  bmc_verification_oraclet::counterexamplet &input_values;
  const bmc_verification_oraclet::candidatet::constantst &constants;
public:
  build_counterexamplet(bmc_verification_oraclet::counterexamplet &ce,
      const bmc_verification_oraclet::candidatet::constantst &constants) :
      input_values(ce), constants(constants)
  {
  }

  void operator()(const goto_tracet::stepst::value_type &step) const
  {
    if (!step.is_assignment()) return;
    if (step.pc->source_location.get_file().empty()) return;
    const irep_idt &symbol_id(step.lhs_object.get_identifier());
    const std::string &name=id2string(symbol_id);
    if (!is_part_of_counterexample(name)) return;
    input_values[symbol_id]=step.full_lhs_value;
  }
};

class constant_inserter
{
  symbol_table_adaptert st_adapter;
  goto_functionst &gf;
  source_location_factoryt lfactory;
public:
  constant_inserter(symbol_tablet &st, goto_functionst &gf) :
      st_adapter(st), gf(gf)
  {
  }
  void operator()(const std::pair<const irep_idt, exprt> &constant)
  {
    const source_locationt loc(lfactory(SYNTHESIS_INIT));
    const exprt &value=constant.second;
    st_adapter.add_global_constant(constant.first, value, gf, loc);
  }
};
}

void bmc_verification_oraclet::verify(const candidatet &candidate)
{
  current_counterexample.clear();
  symbol_tablet symbol_table(this->symbol_table);
  goto_functionst goto_functions;
  goto_functions.copy_from(this->goto_functions);
  const constant_inserter add_constant(symbol_table, goto_functions);
  const candidatet::constantst &constants=candidate.constants;
  std::for_each(constants.begin(), constants.end(), add_constant);
  const candidatet::bodiest &bodies=candidate.bodies;
  const insert_bodyt insert_body(goto_functions);
  std::for_each(bodies.begin(), bodies.end(), insert_body);

  //get solver
  null_message_handlert null_message_handler;
  cbmc_solverst cbmc_solvers(options, symbol_table, null_message_handler);
  std::unique_ptr<cbmc_solverst::solvert> cbmc_solver = 
    cbmc_solvers.get_solver();
  prop_convt& prop_conv = cbmc_solver->prop_conv();
  bmct bmc(options, symbol_table, null_message_handler, prop_conv);

  const safety_checkert::resultt bmc_result=bmc(goto_functions);
  switch (bmc_result)
  {
  case safety_checkert::ERROR:
    is_failure=true;
  case safety_checkert::SAFE:
    return;
  default:
    const goto_tracet::stepst &trace=bmc.safety_checkert::error_trace.steps;
    const build_counterexamplet build_ce(current_counterexample, constants);
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
