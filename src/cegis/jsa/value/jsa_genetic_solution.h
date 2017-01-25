/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SOLUTION_H
#define CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SOLUTION_H

#include <vector>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>

/**
 * @brief
 *
 * @details
 */
#define OPERANDS_PER_JSA_INVARIANT_INSTRUCTION 1

/**
 * @brief
 *
 * @details
 */
#define OPERANDS_PER_JSA_PREDICATE_INSTRUCTION 4

/**
 * @brief
 *
 * @details
 */
#define OPERANDS_PER_JSA_QUERY_INSTRUCTION 3

/**
 * @brief
 *
 * @details
 */
class jsa_genetic_solutiont
{
public:
  /**
   * @brief
   *
   * @details
   */
  typedef std::vector<__CPROVER_jsa_pred_instructiont> predicatet;

  /**
   * @brief
   *
   * @details
   */
  typedef std::vector<predicatet> predicatest;

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
  typedef std::vector<__CPROVER_jsa_query_instructiont> queryt;

  /**
   * @brief
   *
   * @details
   */
  queryt query;

  /**
   * @brief
   *
   * @details
   */
  typedef std::vector<__CPROVER_jsa_invariant_instructiont> invariantt;

  /**
   * @brief
   *
   * @details
   */
  invariantt invariant;

  /**
   * @brief
   *
   * @details
   */
  typedef size_t fitnesst;

  /**
   * @brief
   *
   * @details
   */
  fitnesst fitness;
};

/**
 * @brief
 *
 * @details
 */
typedef std::vector<jsa_genetic_solutiont> jsa_populationt;

#endif // CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SOLUTION_H
