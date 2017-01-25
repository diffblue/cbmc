/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_GENETIC_DYNAMIC_SAFETY_TEST_RUNNER_H
#define CPROVER_CEGIS_SAFETY_GENETIC_DYNAMIC_SAFETY_TEST_RUNNER_H

#include <functional>

#include <util/expr.h>
#include <util/tempfile.h>

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 */
class dynamic_safety_test_runnert
{
public:
  typedef int (*fitness_testert)(const unsigned int[]);
  typedef void *lib_handlet;
private:
  const std::function<std::string(void)> source_code_provider;
  const std::function<size_t(size_t)> max_prog_sz;
  const temporary_filet shared_library;
  lib_handlet handle;
  fitness_testert fitness_tester;
public:
  typedef class safety_goto_cet counterexamplet;
  typedef program_individualt individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param source_code_provider
   * @param max_prog_sz
   */
  dynamic_safety_test_runnert(
      const std::function<std::string(void)> &source_code_provider,
      const std::function<size_t(size_t)> &max_prog_sz);

  /**
   * @brief
   *
   * @details
   */
  ~dynamic_safety_test_runnert();

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   * @param ce
   * @param on_complete
   */
  void run_test(individualt &ind, const counterexamplet &ce,
      std::function<void(bool)> on_complete);

  /**
   * @brief
   *
   * @details
   */
  void join();
};

#endif // CPROVER_CEGIS_SAFETY_GENETIC_DYNAMIC_SAFETY_TEST_RUNNER_H
