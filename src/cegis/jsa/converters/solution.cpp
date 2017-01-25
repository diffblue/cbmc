/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/converters/translate_to_goto_program.h>
#include <cegis/jsa/converters/solution.h>

jsa_solutiont convert(const jsa_genetic_solutiont &solution,
    const jsa_programt &prog)
{
  jsa_solutiont result;
  for (const jsa_genetic_solutiont::predicatest::value_type &pred : solution.predicates)
  {
    result.predicates.push_back(goto_programt::instructionst());
    convert(result.predicates.back(), prog, pred);
  }
  convert(result.query, prog, solution.query);
  convert(result.invariant, prog, solution.invariant);
  return result;
}
