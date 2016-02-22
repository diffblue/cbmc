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
template<class progt, class configt>
class concrete_fitness_source_providert
{
  const progt &prog;
  configt learn_config;
  const std::function<size_t(void)> max_size;
  const std::string execute_func_name;
  std::string source;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   * @param max_size
   * @param execute_func_name
   */
  concrete_fitness_source_providert(const progt &prog,
      std::function<size_t(void)> max_size,
      const std::string &execute_func_name);

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

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param st
 * @param gf
 * @param num_ce_vars
 * @param num_vars
 * @param num_consts
 * @param max_prog_size
 * @param exec_func_name
 */
std::string &post_process_fitness_source(std::string &result,
    const symbol_tablet &st, const goto_functionst &gf, size_t num_ce_vars,
    size_t num_vars, size_t num_consts, size_t max_prog_size,
    const std::string &exec_func_name);

#include "concrete_fitness_source_provider.inc"

#endif /* CEGIS_CONCRETE_FITNESS_SOURCE_PROVIDER_H_ */
