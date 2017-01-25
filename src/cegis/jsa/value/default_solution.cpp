/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/converters/solution.h>
#include <cegis/jsa/value/default_solution.h>

jsa_solutiont default_jsa_solution(const jsa_programt &prog)
{
  jsa_genetic_solutiont result;
  result.fitness=0;
  const jsa_genetic_solutiont::invariantt::value_type inv={ 0 };
  result.invariant.push_back(inv);
  jsa_genetic_solutiont::predicatet pred;
  const jsa_genetic_solutiont::predicatet::value_type pred_instr={ 0, 0, 0, 0 };
  pred.push_back(pred_instr);
  result.predicates.push_back(pred);
  const jsa_genetic_solutiont::queryt::value_type query_prefix={ 0, 0, 0 };
  const jsa_genetic_solutiont::queryt::value_type query_instr={ FILTER, 0, __CPROVER_jsa_null };
  result.query.push_back(query_prefix);
  result.query.push_back(query_instr);
  return convert(result, prog);
}
