/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/value/program_individual_serialisation.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/symex/learn/solution_factory.h>
#include <cegis/safety/value/individual_to_safety_solution_deserialiser.h>

individual_to_safety_solution_deserialisert::individual_to_safety_solution_deserialisert(
    const safety_programt &prog, instruction_set_info_factoryt &info_fac) :
    prog(prog), info_fac(info_fac)
{
}

void individual_to_safety_solution_deserialisert::operator()(
    safety_goto_solutiont &result, const irept &sdu) const
{
  program_individualt ind;
  deserialise(ind, sdu);
  operand_variable_idst ids;
  const symbol_tablet &st=prog.st;
  get_invariant_variable_ids(st, ids);
  create_safety_solution(result, st, prog.gf, ind, ids, info_fac);
}
