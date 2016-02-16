/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONCRETE_FITNESS_SOURCE_PROVIDER_H_
#define CEGIS_CONCRETE_FITNESS_SOURCE_PROVIDER_H_

#include <functional>

#include <cegis/danger/symex/learn/danger_learn_config.h>

/**
 * @brief
 *
 * @details
 */
class concrete_fitness_source_providert
{
  const danger_programt &prog;
  const std::function<size_t(void)> max_size;
  danger_learn_configt learn_config;
  std::string source;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   * @param max_size
   */
  concrete_fitness_source_providert(const danger_programt &prog,
      std::function<size_t(void)> max_size);

  /**
   * @brief
   *
   * @details
   */
  ~concrete_fitness_source_providert();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::string operator()();
};

#endif /* CEGIS_CONCRETE_FITNESS_SOURCE_PROVIDER_H_ */
