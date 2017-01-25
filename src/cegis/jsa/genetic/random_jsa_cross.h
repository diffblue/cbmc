/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_RANDOM_JSA_CROSS_H
#define CPROVER_CEGIS_JSA_GENETIC_RANDOM_JSA_CROSS_H

#include <deque>

#include <cegis/jsa/value/jsa_genetic_solution.h>

/**
 * @brief
 *
 * @details
 */
class random_jsa_crosst
{
  const class jsa_randomt &random;
public:
  typedef jsa_populationt populationt;
  typedef std::deque<populationt::iterator> individualst;
  typedef populationt::value_type individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param random
   */
  explicit random_jsa_crosst(const jsa_randomt &random);

  /**
   * @brief
   *
   * @details
   *
   * @param parents
   * @param children
   */
  void operator()(
      const individualst &parents,
      const individualst &children) const;
};

#endif // CPROVER_CEGIS_JSA_GENETIC_RANDOM_JSA_CROSS_H
