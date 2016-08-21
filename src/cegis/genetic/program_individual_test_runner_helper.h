/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_GENETIC_PROGRAM_INDIVIDUAL_TEST_RUNNER_HELPER_H_
#define CEGIS_GENETIC_PROGRAM_INDIVIDUAL_TEST_RUNNER_HELPER_H_

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @param source
 * @param danger
 */
void implement_program_individual_deserialise(std::string &source, bool danger);

/**
 * @brief
 *
 * @details
 *
 * @param source
 * @param danger
 */
void transform_program_individual_main_to_lib(std::string &source, bool danger);

#endif /* CEGIS_GENETIC_PROGRAM_INDIVIDUAL_TEST_RUNNER_HELPER_H_ */
