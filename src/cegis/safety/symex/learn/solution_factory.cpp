/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <goto-programs/goto_trace.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/genetic/instruction_set_info_factory.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/value/program_individual_serialisation.h>
#include <cegis/instructions/instruction_set_factory.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/symex/learn/replace_operators.h>
#include <cegis/safety/meta/meta_variable_names.h>
#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/symex/learn/solution_factory.h>

namespace
{
const goto_programt &get_execute_body(const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &function_map=gf.function_map;
  const function_mapt::const_iterator it=function_map.find(DANGER_EXECUTE);
  assert(function_map.end() != it);
  assert(it->second.body_available());
  return it->second.body;
}

void copy_instructions(goto_programt::instructionst &prog,
    const symbol_tablet &st, const invariant_variable_namest &var_names,
    const invariant_variable_namest &result_var_names,
    const program_individualt::instructiont &instr,
    const instruction_sett::value_type::second_type &entry,
    const size_t instr_idx)
{
  copy_instructionst copy_instr;
  for (goto_programt::const_targett it=entry.begin(); it != entry.end(); ++it)
  {
    prog.push_back(goto_programt::instructiont());
    goto_programt::targett new_instr=prog.end();
    copy_instr(--new_instr, it);
  }
  copy_instr.finalize();
  goto_programt::targett first=prog.end();
  std::advance(first, -entry.size());
  const program_individualt::instructiont::opst &ops=instr.ops;
  const size_t empty_op=0u;
  const size_t op0=!ops.empty() ? ops.front() : empty_op;
  const size_t op1=ops.size() >= 2 ? ops.at(1) : empty_op;
  const size_t op2=ops.size() >= 3 ? ops.at(2) : empty_op;
  replace_ops_in_instr(st, DANGER_EXECUTE, first, prog.end(), var_names,
      result_var_names, op0, op1, op2, instr_idx);
}

void extract_program(goto_programt::instructionst &prog,
    const symbol_tablet &st, const instruction_sett &instr_set,
    const invariant_variable_namest &var_names,
    const invariant_variable_namest &result_var_names,
    const program_individualt::programt &instructions)
{
  size_t instr_idx=0;
  for (const program_individualt::instructiont &instr : instructions)
  {
    const program_individualt::instructiont::opcodet opcode=instr.opcode;
    const instruction_sett::const_iterator instr_entry=instr_set.find(opcode);
    assert(instr_set.end() != instr_entry);
    copy_instructions(prog, st, var_names, result_var_names, instr,
        instr_entry->second, instr_idx++);
  }
}

void extract_program(goto_programt::instructionst &prog,
    const symbol_tablet &st, const instruction_sett &instr_set,
    const invariant_variable_namest &vars,
    const invariant_variable_namest &rvars,
    const exprt::operandst &instructions)
{
  program_individualt::programt converted(instructions.size());
  std::transform(instructions.begin(), instructions.end(), converted.begin(),
      [](const exprt &instruction)
      { return to_program_individual_instruction(to_struct_expr(instruction));});
  extract_program(prog, st, instr_set, vars, rvars, converted);
}

size_t create_temps(invariant_variable_namest &rnames, const size_t num_tmp)
{
  for (size_t i=0; i < num_tmp; ++i)
    rnames.insert(std::make_pair(i, get_cegis_meta_name(get_tmp(i))));
  return num_tmp;
}

void set_result_var(invariant_variable_namest &result_var_names,
    const size_t var_idx, const size_t loop_idx)
{
  result_var_names.erase(var_idx);
  const std::string result_name(get_cegis_meta_name(get_Ix(loop_idx)));
  result_var_names.insert(std::make_pair(var_idx, result_name));
}
}

void create_safety_solution(safety_goto_solutiont &solution,
    const safety_programt &prog, const goto_tracet &trace,
    const operand_variable_idst &var_ids, const size_t max_sz)
{
  solution.clear();
  const goto_programt &execute_body=get_execute_body(prog.gf);
  const instruction_sett instr_set(extract_instruction_set(execute_body));
  invariant_variable_namest var_names;
  reverse_invariant_var_ids(var_names, var_ids);
  invariant_variable_namest result_var_names;
  assert(max_sz > 0);
  const size_t idx=create_temps(result_var_names, max_sz - 1);
  size_t loop_idx=0;
  for (const goto_trace_stept &step : trace.steps)
  {
    if (!is_program_individual_decl(step)) continue;
    const exprt::operandst &instrs=step.full_lhs_value.operands();
    set_result_var(result_var_names, idx, loop_idx++);
    solution.push_back(goto_programt::instructionst());
    extract_program(solution.back(), prog.st, instr_set, var_names,
        result_var_names, instrs);
  }
}

namespace
{
void create_safety_solution(safety_goto_solutiont &solution,
    const symbol_tablet &st, const goto_functionst &gf,
    const program_individualt &ind, const operand_variable_idst &var_ids,
    const instruction_sett &instr_set)
{
  solution.clear();
  invariant_variable_namest vars;
  reverse_invariant_var_ids(vars, var_ids);
  size_t loop_idx=0;
  for (const program_individualt::programt &instrs : ind.programs)
  {
    invariant_variable_namest rvars;
    const size_t prog_size=instrs.size();
    const size_t idx=prog_size > 0 ? create_temps(rvars, prog_size - 1) : 0;
    set_result_var(rvars, idx, loop_idx++);
    solution.push_back(goto_programt::instructionst());
    extract_program(solution.back(), st, instr_set, vars, rvars, instrs);
  }
}
}

void create_safety_solution(safety_goto_solutiont &solution,
    const symbol_tablet &st, const goto_functionst &gf,
    const program_individualt &ind, const operand_variable_idst &var_ids)
{
  const goto_programt &execute_body=get_execute_body(gf);
  const instruction_sett instr_set(extract_instruction_set(execute_body));
  create_safety_solution(solution, st, gf, ind, var_ids, instr_set);
}

void create_safety_solution(safety_goto_solutiont &solution,
    const symbol_tablet &st, const goto_functionst &gf,
    const program_individualt &ind, const operand_variable_idst &var_ids,
    instruction_set_info_factoryt &info_fac)
{
  const instruction_sett &instr_set=info_fac.get_instructions();
  create_safety_solution(solution, st, gf, ind, var_ids, instr_set);
}
