/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_CONCRETE_TEST_RUNNER_H_
#define CEGIS_GENETIC_CONCRETE_TEST_RUNNER_H_

#include <functional>

#include <util/expr.h>
#include <util/tempfile.h>

#include <cegis/cegis-util/task_pool.h>

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
class concrete_test_runnert
{
  const std::function<std::string(void)> source_code_provider;
  const temporary_filet executable;
  bool executable_compiled;
  task_poolt task_pool;
public:
  typedef std::map<const irep_idt, exprt> counterexamplet;
  typedef program_individualt individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param source_code_provider
   */
  concrete_test_runnert(std::function<std::string(void)> source_code_provider);

  /**
   * @brief
   *
   * @details
   */
  ~concrete_test_runnert();

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   * @param ce
   */
  void run_test(individualt &ind, const counterexamplet &ce);

  /**
   * @brief
   *
   * @details
   */
  void join();
};

#endif /* CEGIS_GENETIC_CONCRETE_TEST_RUNNER_H_ */
