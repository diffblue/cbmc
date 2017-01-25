/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <numeric>

#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/genetic/solution_helper.h>

namespace
{
size_t sum_pred(const size_t sum, const jsa_genetic_solutiont::predicatet &pred)
{
  return sum + pred.size() * OPERANDS_PER_JSA_PREDICATE_INSTRUCTION;
}
}

size_t get_num_genetic_targets(const jsa_genetic_solutiont &solution)
{
  size_t result=solution.invariant.size();
  const jsa_genetic_solutiont::predicatest &preds=solution.predicates;
  result=std::accumulate(preds.begin(), preds.end(), result, sum_pred);
  return result+=solution.query.size() * OPERANDS_PER_JSA_QUERY_INSTRUCTION;
}
