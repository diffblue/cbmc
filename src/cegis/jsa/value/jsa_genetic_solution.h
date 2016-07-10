/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_GENETIC_SOLUTION_H_
#define CEGIS_JSA_GENETIC_SOLUTION_H_

#include <vector>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>

/**
 * @brief
 *
 * @details
 */
class jsa_genetic_solutiont
{
public:
  typedef std::vector<std::vector<__CPROVER_jsa_pred_instructiont> > predicatest;

  /**
   * @brief
   *
   * @details
   */
  predicatest predicates;

  /**
   * @brief
   *
   * @details
   */
  std::vector<__CPROVER_jsa_query_instructiont> query;

  /**
   * @brief
   *
   * @details
   */
  std::vector<__CPROVER_jsa_invariant_instructiont> invariant;
};

#endif /* CEGIS_JSA_GENETIC_SOLUTION_H_ */
