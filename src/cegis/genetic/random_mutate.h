/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_RANDOM_MUTATE_H_
#define CEGIS_GENETIC_RANDOM_MUTATE_H_

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
class random_mutatet
{
  class random_individualt &random;
  const std::function<size_t(void)> num_consts;
public:
  typedef program_individualt individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param random
   * @param num_consts
   */
  random_mutatet(random_individualt &random,
      const std::function<size_t(void)> &num_consts);

  /**
   * @brief
   *
   * @details
   */
  ~random_mutatet();

  /**
   * @brief
   *
   * @details
   *
   * @param lhs
   * @param rhs
   */
  void operator()(individualt &lhs, const individualt &rhs) const;

  /**
   * @brief
   *
   * @details
   *
   * @param lhs
   */
  void havoc(individualt &ind) const;

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   */
  void post_process(program_individualt &ind) const;
};

#endif /* CEGIS_GENETIC_RANDOM_MUTATE_H_ */
