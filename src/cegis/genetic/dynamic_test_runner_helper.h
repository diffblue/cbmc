/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DYNAMIC_TEST_RUNNER_HELPER_H_
#define CEGIS_DYNAMIC_TEST_RUNNER_HELPER_H_

#include <functional>

typedef void *fitness_lib_handlet;

#define LIBRARY_PREFIX "fitness_test"
#ifndef _WIN32
#define LIBRARY_SUFFIX ".so"
#else
#define LIBRARY_SUFFIX ".dll"
#endif

/**
 * @brief
 *
 * @details
 *
 * @param handle
 * @param source_code_provider
 * @param library_file_path
 * @param compile_options
 */
void *prepare_fitness_tester_library(
    fitness_lib_handlet &handle,
    const std::function<std::string(void)> &source_code_provider,
    const std::string &library_file_path,
    const std::string &compile_options);

/**
 * @brief
 *
 * @details
 *
 * @param handle
 * @param fitness_tester
 * @param source_code_provider
 * @param library_file_path
 * @param compile_options
 */
template<class fitness_testert>
void prepare_fitness_tester_library(
    fitness_lib_handlet &handle,
    fitness_testert &fitness_tester,
    const std::function<std::string(void)> &source_code_provider,
    const std::string &library_file_path,
    std::string compile_options = "");

/**
 * @brief
 *
 * @details
 *
 * @param handle
 */
void close_fitness_tester_library(fitness_lib_handlet &handle);

/**
 * @brief
 *
 * @details
 *
 * @param handle
 * @param fitness_tester
 */
template<class fitness_testert>
void close_fitness_tester_library(
    fitness_lib_handlet &handle,
    fitness_testert &fitness_tester);

#include "dynamic_test_runner_helper.inc"

#endif /* CEGIS_DYNAMIC_TEST_RUNNER_HELPER_H_ */
