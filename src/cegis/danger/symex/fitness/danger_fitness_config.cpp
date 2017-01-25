/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/value/program_individual.h>
#include <cegis/genetic/instruction_set_info_factory.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/verify/insert_constraint.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program_printer.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/verify/insert_candidate.h>
#include <cegis/danger/symex/fitness/danger_fitness_config.h>

danger_fitness_configt::danger_fitness_configt(
    instruction_set_info_factoryt &info_fac, const danger_programt &prog) :
    info_fac(info_fac), original_program(prog), constraint_inserted(false), program_contains_ce(
        false), max_solution_size(0u)
{
}

danger_fitness_configt::~danger_fitness_configt()
{
}

void danger_fitness_configt::convert(candidatet &current_candidate,
    const individualt &ind)
{
  operand_variable_idst ids;
  get_invariant_variable_ids(original_program.st, ids);
  const instruction_sett &instrs=info_fac.get_instructions();
  create_danger_solution(current_candidate, original_program, ind, instrs, ids);
}

namespace
{
void fix_quantifiers(const danger_programt &org_prog, danger_programt &new_prog,
    goto_programt::targetst &quantifiers)
{
  goto_programt::const_targett org_off=org_prog.loops.front().meta_variables.Ix;
  --org_off;
  goto_programt::targett new_off=new_prog.loops.front().meta_variables.Ix;
  --new_off;
  goto_programt::targett::difference_type diff;
  for (goto_programt::targett &q : quantifiers)
  {
    diff=std::distance(org_off, static_cast<goto_programt::const_targett>(q));
    q=new_off;
    std::advance(q, diff);
  }
}
}

void danger_fitness_configt::set_candidate(const candidatet &candidate)
{
  if (!constraint_inserted)
  {
    program_with_constraint=original_program;
    const danger_constraint constraint(program_with_constraint.use_ranking);
    invariant_insert_constraint(original_quantifiers, program_with_constraint,
        std::cref(constraint));
    constraint_inserted=true;
  }
  program=program_with_constraint;
  quantifiers=original_quantifiers;
  fix_quantifiers(program_with_constraint, program, quantifiers);
  program_contains_ce=false;
  danger_insert_candidate(program, candidate);
}

void danger_fitness_configt::set_test_case(const counterexamplet &ce)
{
  if (quantifiers.empty()) return;
  goto_functionst &gf=program.gf;
  for (goto_programt::targett quantifier : quantifiers)
  {
    const irep_idt &var=get_affected_variable(*quantifier);
    const counterexamplet::const_iterator it=ce.find(var);
    if (ce.end() == it) continue;
    symbol_tablet &st=program.st;
    if (program_contains_ce)
    {
      goto_programt::targett assignment=quantifier;
      erase_target(get_entry_body(gf).instructions, ++assignment);
    }
    cegis_assign_user_variable(st, gf, quantifier, var, it->second);
  }
  gf.update();
  program_contains_ce=true;
}

const symbol_tablet &danger_fitness_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &danger_fitness_configt::get_goto_functions() const
{
  return program.gf;
}

void danger_fitness_configt::set_max_solution_size(const size_t size)
{
  max_solution_size=size;
}

void danger_fitness_configt::show(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  print_danger_program(os, original_program, candidate);
}
