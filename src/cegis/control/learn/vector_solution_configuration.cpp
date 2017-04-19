/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_vector_solution.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/print_control_solution.h>
#include <cegis/control/learn/vector_solution_configuration.h>

namespace
{
bool is_assignment_to_solution_var(const goto_programt::instructiont &instr)
{
  if(goto_program_instruction_typet::ASSIGN != instr.type) return false;
  const std::string &var_name=id2string(get_affected_variable(instr));
  return CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME == var_name;
}
}

void vector_solution_configurationt::nondeterminise_solution_configuration(
    symbol_tablet &st, goto_functionst &gf)
{
  goto_programt &init_body=get_body(gf, CPROVER_INIT);
  goto_programt::instructionst &init_instrs=init_body.instructions;
  const goto_programt::targett assignment=std::find_if(init_instrs.begin(),
      init_instrs.end(), is_assignment_to_solution_var);
  goto_programt &entry_body=get_entry_body(gf);
  const goto_programt::targett first_entry=entry_body.instructions.begin();
  const goto_programt::targett new_assignment=entry_body.insert_before(
      first_entry);
  new_assignment->source_location=first_entry->source_location;
  new_assignment->type=assignment->type;
  new_assignment->code=assignment->code;
  init_body.instructions.erase(assignment);
  init_body.update();
  entry_body.update();
}

namespace
{
bool is_solution(const goto_trace_stept &step)
{
  const exprt &lhs=step.full_lhs;
  if(ID_symbol != lhs.id()) return false;
  const std::string &id=id2string(to_symbol_expr(lhs).get_identifier());
  return CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME == id;
}

const array_exprt &find_solution(const goto_tracet &trace)
{
  const goto_tracet::stepst &steps=trace.steps;
  const auto it=std::find_if(steps.begin(), steps.end(), is_solution);
  assert(steps.end() != it);
  return to_array_expr(it->full_lhs_value);
}
}

void vector_solution_configurationt::convert(solutiont &current_candidate,
    const goto_tracet &trace, const symbol_tablet &st)
{
  current_candidate.K=find_solution(trace);
}

void vector_solution_configurationt::show_candidate(messaget::mstreamt &os,
    const solutiont &candidate, const symbol_tablet &st)
{
  print_control_array(os, candidate.K, "K", st);
}
