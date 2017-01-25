/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_RANDOM_CROSS_H
#define CPROVER_CEGIS_GENETIC_RANDOM_CROSS_H

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
class random_crosst
{
  class random_individualt &random;
public:
  typedef program_populationt populationt;
  typedef std::deque<populationt::iterator> individualst;
  typedef populationt::value_type::programt programt;

  /**
   * @brief
   *
   * @details
   *
   * @param random
   */
  explicit random_crosst(random_individualt &random);

  /**
   * @brief
   *
   * @details
   */
  ~random_crosst();

  /**
   * @brief
   *
   * @details
   *
   * @param parents
   * @param children
   */
  void operator()(const individualst &parents, const individualst &children);
};

#endif // CPROVER_CEGIS_GENETIC_RANDOM_CROSS_H
