/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/genetic/instruction_set_info_factory.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/invariant/symex/verify/insert_constraint.h>
#include <cegis/safety/value/safety_goto_ce.h>
#include <cegis/safety/options/safety_program_printer.h>
#include <cegis/safety/constraint/safety_constraint_factory.h>
#include <cegis/safety/symex/learn/solution_factory.h>
#include <cegis/safety/symex/verify/insert_candidate.h>
#include <cegis/safety/symex/fitness/safety_fitness_config.h>

safety_fitness_configt::safety_fitness_configt(
    instruction_set_info_factoryt &info_fac, const safety_programt &prog) :
    info_fac(info_fac), original_program(prog), constraint_inserted(false), program_contains_ce(
        false), max_solution_size(0u)
{
}

safety_fitness_configt::~safety_fitness_configt()
{
}

void safety_fitness_configt::convert(candidatet &current_candidate,
    const individualt &ind)
{
  const symbol_tablet &st=original_program.st;
  const goto_functionst &gf=original_program.gf;
  operand_variable_idst ids;
  get_invariant_variable_ids(st, ids);
  create_safety_solution(current_candidate, st, gf, ind, ids, info_fac);
}

namespace
{
void fix_quantifiers(const safety_programt &org_prog, safety_programt &new_prog,
    goto_programt::targetst &quantifiers)
{
  goto_programt::const_targett org_off=
      org_prog.safety_loops.front().meta_variables.Ix;
  --org_off;
  goto_programt::targett new_off=new_prog.safety_loops.front().meta_variables.Ix;
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

void safety_fitness_configt::set_candidate(const candidatet &candidate)
{
  if (!constraint_inserted)
  {
    program_with_constraint=original_program;
    invariant_insert_constraint(original_quantifiers, program_with_constraint,
        create_safety_constraint);
    constraint_inserted=true;
  }
  program=program_with_constraint;
  quantifiers=original_quantifiers;
  fix_quantifiers(program_with_constraint, program, quantifiers);
  program_contains_ce=false;
  safety_insert_candidate(program, candidate);
}

void safety_fitness_configt::set_test_case(const counterexamplet &ce)
{
  if (quantifiers.empty()) return;
  goto_functionst &gf=program.gf;
  // TODO: Implement for multiple loops (change constraint, instrumentation)
  const counterexamplet::assignmentst &ass=ce.x.back();
  typedef counterexamplet::assignmentst counterexamplet;

  for (goto_programt::targett quantifier : quantifiers)
  {
    const irep_idt &var=get_affected_variable(*quantifier);
    const counterexamplet::const_iterator it=ass.find(var);
    if (ass.end() == it) continue;
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

const symbol_tablet &safety_fitness_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &safety_fitness_configt::get_goto_functions() const
{
  return program.gf;
}

void safety_fitness_configt::set_max_solution_size(const size_t size)
{
  max_solution_size=size;
}

void safety_fitness_configt::show(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  print_safety_program(os, original_program, candidate);
}
