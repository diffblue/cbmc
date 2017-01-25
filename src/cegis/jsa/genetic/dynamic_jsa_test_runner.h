/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_DYNAMIC_JSA_TEST_RUNNER_H
#define CPROVER_CEGIS_JSA_GENETIC_DYNAMIC_JSA_TEST_RUNNER_H

#include <functional>

#include <util/tempfile.h>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>
#include <cegis/jsa/value/jsa_counterexample.h>

/**
 * @brief
 *
 * @details
 */
class dynamic_jsa_test_runnert
{
  typedef void *lib_handlet;
public:
  typedef jsa_counterexamplet counterexamplet;
  typedef class jsa_genetic_solutiont individualt;
private:
  typedef int (*fitness_testert)(
      const __CPROVER_jsa_index_t __CPROVER_jsa_query_size,
      const __CPROVER_jsa_query_instructiont *__CPROVER_jsa_query,
      const __CPROVER_jsa_index_t __CPROVER_jsa_invariant_size,
      const __CPROVER_jsa_invariant_instructiont *__CPROVER_jsa_invariant,
      const __CPROVER_jsa_index_t *__CPROVER_jsa_predicate_sizes,
      const __CPROVER_jsa_pred_instructiont **__CPROVER_jsa_predicates,
      const __CPROVER_jsa_abstract_heapt *__CPROVER_jsa_counterexample_heaps,
      const __CPROVER_jsa_word_t *__CPROVER_jsa_counterexample_words);
  const std::function<std::string(void)> source_code;
  const temporary_filet shared_library;
  lib_handlet handle;
  fitness_testert fitness_tester;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param source_code_provider
   */
  explicit dynamic_jsa_test_runnert(
      const std::function<std::string(void)> &source_code_provider);

  /**
   * @brief
   *
   * @details
   */
  ~dynamic_jsa_test_runnert();

  /**
   * @brief
   *
   * @details
   *
   * @param individual
   * @param counterexample
   * @param on_complete
   */
  void run_test(
      individualt &individual,
      const counterexamplet &counterexample,
      std::function<void(bool)> on_complete);

  /**
   * @brief
   *
   * @details
   */
  void join();
};

#endif // CPROVER_CEGIS_JSA_GENETIC_DYNAMIC_JSA_TEST_RUNNER_H
